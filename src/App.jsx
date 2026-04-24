import React, { useState, useEffect, useRef, useMemo, useCallback } from "react";
import * as d3 from "d3";

// ─── TopoJSON → GeoJSON decoder (matches RD Profitability map) ───────────────
// Decodes us-atlas@3 topology arcs into plain GeoJSON features so d3.geoPath
// can project them. Kept inline so the file stays self-contained.
// ─── Geographic distance — haversine in miles ───────────────────────────────
// Used by compartment planner to decide which deliveries are close enough to
// combine into a single multi-stop truck. Earth radius = 3958.8 mi.
function distMiles(lat1, lng1, lat2, lng2) {
  const toRad = (d) => d * Math.PI / 180;
  const R = 3958.8;
  const dLat = toRad(lat2 - lat1);
  const dLng = toRad(lng2 - lng1);
  const a = Math.sin(dLat/2)**2 +
            Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLng/2)**2;
  return 2 * R * Math.asin(Math.sqrt(a));
}


// ─── Compartment Pocket Planner ─────────────────────────────────────────────
// Given a list of pending plan rows (one per store+grade) and the carrier
// fleet, group rows into "trips" — each trip = one truck, one terminal,
// up to N stops where each stop's volume fits in one compartment.
//
// Algorithm (greedy, transparent, defensible):
//   1. Bucket rows by their chosen terminal — multi-stop trips can only
//      pick up from a single rack.
//   2. Within each bucket, build clusters of rows whose stores are within
//      MAX_CLUSTER_RADIUS miles of each other (single-link agglomerative).
//   3. For each cluster, pick the best-fitting available carrier (one whose
//      compartment configuration can hold the largest deliveries with
//      minimal slack) and pack rows into compartments using first-fit-
//      decreasing — bin-packing is NP-hard but FFD is within ~22% of optimum
//      and is the only honest approach to demo in a browser.
//   4. Each pack-result = one trip with 1+ stops. Rows that don't fit get
//      their own single-stop trip.
//
// Returned trips include savings vs. running each row as its own truck —
// the consolidation savings come from amortising the carrier base rate
// across multiple stops and fewer billable miles.
const MAX_CLUSTER_RADIUS_MI = 35;     // 35 mi keeps trips < ~75 mi route
const STOP_TIME_MIN = 25;             // typical drop time per stop
const SLACK_PENALTY_FACTOR = 0.10;    // prefer trucks with less wasted compartment space

function planCompartmentTrips(rows, carrierFleet) {
  if (!rows || rows.length === 0) return [];

  // Bucket by terminal id
  const byTerminal = {};
  rows.forEach(r => {
    const tid = r.chosen?.terminal?.id;
    if (!tid) return;
    (byTerminal[tid] = byTerminal[tid] || []).push(r);
  });

  const trips = [];
  let tripCounter = 1;

  Object.entries(byTerminal).forEach(([terminalId, terminalRows]) => {
    // ── Step 2: cluster by proximity (single-link agglomerative) ─────────
    const remaining = terminalRows.slice();
    const clusters = [];
    while (remaining.length > 0) {
      const cluster = [remaining.shift()];
      let added = true;
      while (added) {
        added = false;
        for (let i = remaining.length - 1; i >= 0; i--) {
          const cand = remaining[i];
          const closeToCluster = cluster.some(c =>
            distMiles(c.store.lat, c.store.lng, cand.store.lat, cand.store.lng) <= MAX_CLUSTER_RADIUS_MI
          );
          if (closeToCluster) {
            cluster.push(cand);
            remaining.splice(i, 1);
            added = true;
          }
        }
      }
      clusters.push(cluster);
    }

    // ── Step 3+4: pack each cluster into trucks ────────────────────────
    clusters.forEach(cluster => {
      // Carriers that have terminal access AND have available trucks
      const eligibleCarriers = carrierFleet
        .filter(c => c.terminalAccess?.includes(terminalId) && c.available > 0);
      if (eligibleCarriers.length === 0) {
        // No carrier — emit each row as its own (unassignable) trip so
        // the dispatcher still sees them in the list.
        cluster.forEach(r => trips.push({
          id: `T${String(tripCounter++).padStart(3,"0")}`,
          terminal: r.chosen.terminal, carrier: null, stops:[r], rows:[r],
          totalGals: r.vol, slack: 0, slackPct: 0, isMultiStop: false,
          unassigned: true, savings: 0, baselineCost: 0, tripCost: 0,
          mileage: 0,
        }));
        return;
      }

      // Sort cluster rows by volume desc — first-fit-decreasing
      const sortedRows = cluster.slice().sort((a,b) => b.vol - a.vol);
      const unassignedRows = sortedRows.slice();

      while (unassignedRows.length > 0) {
        // Pick the carrier whose compartment config best matches the
        // largest remaining rows. Score = how many of the top rows we
        // can pack into the truck's compartments with minimal slack.
        let bestCarrier = null, bestPlan = null, bestScore = -Infinity;
        for (const carrier of eligibleCarriers) {
          const compartments = (carrier.compartments || []).slice().sort((a,b) => b - a);
          const plan = [];
          const compRemaining = compartments.map(c => ({ cap:c, free:c, fills:[] }));
          for (const row of unassignedRows) {
            // First-fit-decreasing: drop into the smallest compartment
            // that can still hold this row's volume.
            const fitting = compRemaining
              .filter(c => c.free >= row.vol && c.fills.length === 0)
              .sort((a,b) => a.cap - b.cap)[0];
            if (fitting) {
              fitting.fills.push(row);
              fitting.free = 0;  // one product per compartment to avoid contamination
              plan.push(row);
            }
          }
          if (plan.length === 0) continue;
          const totalCap = compartments.reduce((s,c) => s + c, 0);
          const usedGals = plan.reduce((s,r) => s + r.vol, 0);
          const slack = totalCap - usedGals;
          const slackPct = totalCap > 0 ? slack / totalCap : 1;
          // Score: maximize stops, penalize slack
          const score = plan.length - SLACK_PENALTY_FACTOR * slackPct * 10;
          if (score > bestScore) {
            bestScore = score;
            bestCarrier = carrier;
            bestPlan = { rows:plan, compartments:compRemaining, totalCap, usedGals, slack, slackPct };
          }
        }

        if (!bestCarrier || !bestPlan || bestPlan.rows.length === 0) {
          // Truly unassignable — emit a single-row trip and continue
          const r = unassignedRows.shift();
          trips.push({
            id: `T${String(tripCounter++).padStart(3,"0")}`,
            terminal: r.chosen.terminal, carrier: null, stops:[r], rows:[r],
            totalGals: r.vol, slack: 0, slackPct: 0, isMultiStop: false,
            unassigned: true, savings: 0, baselineCost: 0, tripCost: 0,
            mileage: 0,
          });
          continue;
        }

        // Build the trip from terminal → stops in nearest-neighbor order
        const stops = bestPlan.rows.slice();
        const ordered = [];
        let lastLat = bestPlan.rows[0].chosen.terminal ? null : null;
        // Use terminal lat/lng as the trip origin
        const origin = bestPlan.rows[0].chosen.terminal;
        let curLat = origin.lat, curLng = origin.lng;
        const remainingStops = stops.slice();
        while (remainingStops.length > 0) {
          let bestIdx = 0, bestD = Infinity;
          for (let i = 0; i < remainingStops.length; i++) {
            const s = remainingStops[i].store;
            const d = distMiles(curLat, curLng, s.lat, s.lng);
            if (d < bestD) { bestD = d; bestIdx = i; }
          }
          const next = remainingStops.splice(bestIdx, 1)[0];
          ordered.push(next);
          curLat = next.store.lat; curLng = next.store.lng;
        }

        // Total trip mileage (terminal → s1 → s2 → ... → terminal)
        let mileage = 0;
        let pLat = origin.lat, pLng = origin.lng;
        ordered.forEach(s => {
          mileage += distMiles(pLat, pLng, s.store.lat, s.store.lng);
          pLat = s.store.lat; pLng = s.store.lng;
        });
        mileage += distMiles(pLat, pLng, origin.lat, origin.lng); // return leg

        // Cost: carrier base rate × gallons + per-mile rate × mileage
        const tripCost = bestCarrier.rateBase * bestPlan.usedGals
                       + (bestCarrier.ratePerMile || 0) * mileage;
        // Baseline = each stop runs as its own truck (each pays full base rate
        // and individual round-trip mileage)
        const baselineCost = ordered.reduce((sum,r) => {
          const indMiles = 2 * distMiles(origin.lat, origin.lng, r.store.lat, r.store.lng);
          return sum + bestCarrier.rateBase * r.vol + (bestCarrier.ratePerMile || 0) * indMiles;
        }, 0);
        const savings = baselineCost - tripCost;

        trips.push({
          id: `T${String(tripCounter++).padStart(3,"0")}`,
          terminal: origin,
          carrier: bestCarrier,
          stops: ordered,
          rows: ordered,
          compartments: bestPlan.compartments,
          totalCap: bestPlan.totalCap,
          totalGals: bestPlan.usedGals,
          slack: bestPlan.slack,
          slackPct: bestPlan.slackPct,
          isMultiStop: ordered.length > 1,
          unassigned: false,
          mileage,
          tripCost, baselineCost, savings,
        });

        // Remove packed rows from unassigned
        const packedIds = new Set(ordered.map(r => r.id));
        for (let i = unassignedRows.length - 1; i >= 0; i--) {
          if (packedIds.has(unassignedRows[i].id)) unassignedRows.splice(i, 1);
        }
      }
    });
  });

  return trips;
}


function topoFeatures(topology, objectName) {
  const obj = topology.objects[objectName];
  const sc = topology.transform?.scale     || [1,1];
  const tr = topology.transform?.translate || [0,0];
  const arcs = topology.arcs.map(arc => {
    let x=0,y=0;
    return arc.map(pt => { x+=pt[0]; y+=pt[1]; return [x*sc[0]+tr[0], y*sc[1]+tr[1]]; });
  });
  function stitchRing(indices) {
    const coords=[];
    indices.forEach((idx,i) => {
      const fwd=idx>=0;
      const pts=fwd?arcs[idx]:[...arcs[~idx]].reverse();
      coords.push(...(i===0?pts:pts.slice(1)));
    });
    return coords;
  }
  function geomToFeature(geom) {
    if(!geom) return null;
    if(geom.type==="Polygon")      return {type:"Feature",id:geom.id,properties:geom.properties||{},geometry:{type:"Polygon",     coordinates:geom.arcs.map(stitchRing)}};
    if(geom.type==="MultiPolygon") return {type:"Feature",id:geom.id,properties:geom.properties||{},geometry:{type:"MultiPolygon",coordinates:geom.arcs.map(p=>p.map(stitchRing))}};
    return null;
  }
  return (obj.geometries||[]).map(geomToFeature).filter(Boolean);
}

// FIPS codes visible on the SE US map. Includes neighbors so state borders
// render cleanly even though we don't serve stores in all of them.
const SE_SHOW_FIPS = new Set([
  "37", // NC
  "45", // SC
  "51", // VA
  "13", // GA
  "12", // FL
  "47", // TN
  "01", // AL
  "28", // MS
  "54", // WV
  "21", // KY
  "24", // MD
  "10", // DE
  "11", // DC
]);
// States where we actually have stores — painted brighter (market states).
const SE_MARKET_FIPS = new Set(["37","45","51","13","12","01"]);
const SE_FIPS_ABBR = {
  "37":"NC","45":"SC","51":"VA","13":"GA","12":"FL","47":"TN","01":"AL","28":"MS",
  "54":"WV","21":"KY","24":"MD","10":"DE","11":"DC",
};

// ─── Real pipeline routes (lng,lat waypoints) ────────────────────────────────
// Geometry sourced from the EIA Petroleum Product Pipelines shapefile
// (U.S. Energy Information Administration), originally in Web Mercator
// (EPSG:3857) and reprojected to WGS84 lng/lat. Colonial and Plantation
// polylines identified by their endpoint geography: Houston → Linden NJ
// for Colonial (68 vertices), Baton Rouge → Newington VA for Plantation
// (14 vertices). Segments outside the visible SE-US viewport get clipped
// automatically by the SVG viewBox — they're still projected correctly,
// just off-canvas.
// Colonial Pipeline — Houston, TX → Linden, NJ (~5,500 mi, 68 waypoints)
//   Real geometry from EIA Petroleum Product Pipelines shapefile, reprojected
//   from Web Mercator (EPSG:3857) to WGS84. Two parallel mainlines (Line 1 =
//   gasoline, Line 2 = distillates) converge at the Greensboro, NC tank farm,
//   then a Northeast segment continues to Linden, NJ.
const COLONIAL_ROUTE = [
  [-95.1921, 29.7490],
  [-95.1692, 29.8236],
  [-94.2884, 29.9050],
  [-93.2967, 30.1612],
  [-92.5059, 30.4165],
  [-91.7480, 30.5265],
  [-91.4350, 30.7154],
  [-91.3342, 30.6960],
  [-91.2708, 30.7142],
  [-89.5106, 31.6263],
  [-88.7456, 32.3505],
  [-88.0485, 32.7838],
  [-87.6282, 32.9822],
  [-86.7799, 33.2832],
  [-85.7761, 33.6149],
  [-84.6843, 33.8602],
  [-84.4756, 33.8809],
  [-84.3981, 33.9518],
  [-83.4196, 33.9857],
  [-81.8744, 34.9234],
  [-80.9274, 35.2793],
  [-79.9178, 36.0770],
  [-78.2465, 37.6508],
  [-77.7109, 38.5920],
  [-77.5058, 38.8024],
  [-77.4080, 38.9190],
  [-77.0371, 39.3655],
  [-76.9073, 39.5009],
  [-76.6831, 39.5594],
  [-76.4984, 39.5499],
  [-75.9507, 39.7218],
  [-75.7917, 39.7642],
  [-75.6527, 39.8302],
  [-75.5831, 39.8474],
  [-75.5294, 39.8398],
  [-75.5019, 39.8499],
  [-75.4796, 39.8370],
  [-75.4692, 39.8346],
  [-75.4634, 39.8247],
  [-75.4442, 39.8153],
  [-75.4328, 39.8016],
  [-75.4176, 39.7878],
  [-75.3812, 39.7922],
  [-75.3723, 39.7853],
  [-75.3316, 39.7855],
  [-75.2813, 39.7945],
  [-75.2017, 39.8192],
  [-75.1796, 39.8062],
  [-75.0999, 39.8552],
  [-75.0327, 39.8662],
  [-74.9347, 39.9433],
  [-74.8961, 39.9760],
  [-74.8413, 40.0057],
  [-74.8137, 40.0286],
  [-74.6655, 40.1466],
  [-74.6369, 40.1733],
  [-74.5202, 40.2463],
  [-74.4458, 40.4123],
  [-74.3896, 40.4930],
  [-74.3607, 40.5174],
  [-74.3255, 40.5341],
  [-74.2768, 40.5480],
  [-74.2560, 40.5666],
  [-74.2292, 40.5960],
  [-74.2130, 40.6205],
  [-74.1818, 40.6320],
  [-74.1816, 40.6665],
  [-74.1260, 40.7082],
];
// Plantation Pipeline — Baton Rouge, LA → Newington/DC area (~3,100 mi, 14 waypoints)
//   Real geometry from EIA Petroleum Product Pipelines shapefile, reprojected
//   from Web Mercator to WGS84. Parallels much of Colonial's route and
//   terminates near Washington, DC.
const PLANTATION_ROUTE = [
  [-91.1924, 30.4843],
  [-89.5339, 31.6334],
  [-88.7251, 32.4071],
  [-86.8186, 33.2905],
  [-85.1429, 33.7005],
  [-84.1425, 33.9670],
  [-83.4044, 33.9973],
  [-81.8744, 34.9234],
  [-80.9254, 35.2812],
  [-79.8261, 36.1419],
  [-77.5790, 37.4711],
  [-77.2648, 38.5597],
  [-77.1905, 38.7339],
  [-77.0328, 38.8417],
];

//  THEME 
function makeTheme(dark) {
  return dark ? {
    navBg:"#0D1B2A", navBorder:"#1B263B", tickerBg:"#080E18", bodyBg:"#080E18",
    cardBg:"#111D2E", cardBord:"#1B263B",
    textPri:"#E8EDF6", textSec:"#BBD5EF", textMut:"#3E6387",
    gold:"#F4D398", green:"#22C55E", amber:"#FBBF24", red:"#F87171", blue:"#BBD5EF",
  } : {
    navBg:"#0D1B2A", navBorder:"#1B263B", tickerBg:"#080E18", bodyBg:"#F0F2F5",
    cardBg:"#FFFFFF", cardBord:"#DDE3EC",
    textPri:"#0D1B2A", textSec:"#3E6387", textMut:"#848270",
    gold:"#F4D398", green:"#16A34A", amber:"#D97706", red:"#DC2626", blue:"#3E6387",
  };
}

//  DATA 
const TERMINALS = [
  { id:"selma",      name:"Selma, NC",        short:"SEL", lat:35.53, lng:-78.29, pipeline:"Colonial",   supplier:"Valero" },
  { id:"apex",       name:"Apex, NC",          short:"APX", lat:35.73, lng:-78.85, pipeline:"Colonial",   supplier:"Marathon" },
  { id:"charlotte",  name:"Charlotte, NC",     short:"CLT", lat:35.22, lng:-80.84, pipeline:"Colonial",   supplier:"Shell" },
  { id:"richmond",   name:"Richmond, VA",      short:"RIC", lat:37.54, lng:-77.43, pipeline:"Colonial",   supplier:"ExxonMobil" },
  { id:"atlanta",    name:"Doraville, GA",     short:"ATL", lat:33.90, lng:-84.28, pipeline:"Colonial",   supplier:"Valero" },
  { id:"macon",      name:"Macon, GA",         short:"MCN", lat:32.84, lng:-83.63, pipeline:"Colonial",   supplier:"Marathon" },
  { id:"bainbridge", name:"Bainbridge, GA",    short:"BNG", lat:30.90, lng:-84.57, pipeline:"Plantation", supplier:"Citgo" },
  { id:"birmingham", name:"Birmingham, AL",    short:"BHM", lat:33.52, lng:-86.81, pipeline:"Colonial",   supplier:"Marathon" },
  { id:"jacksonville",name:"Jacksonville, FL", short:"JAX", lat:30.33, lng:-81.66, pipeline:"Plantation", supplier:"Shell" },
  { id:"tampa",      name:"Tampa, FL",         short:"TPA", lat:27.95, lng:-82.46, pipeline:"Plantation", supplier:"ExxonMobil" },
];

// Physical grades that exist as discrete tanks at the store and that we buy
// from the rack. Plus (87 octane) is NOT in this list — Plus is blended at
// the dispenser from Regular and Premium, so it has no rack price and no
// dedicated tank. The optimizer, compartment planner, and inventory tank
// model all key off this list.
const GRADES = ["Regular", "Premium", "Diesel"];
// Procurement grades = what we actually buy from terminals. Same as GRADES
// for now (no other blended products), but kept as a separate name so the
// distinction is explicit at every callsite that matters.
const PROCUREMENT_GRADES = GRADES;
// Sales grades = what we sell at the pump, including blended products.
// Plus appears here but not in GRADES because it's a blend, not a SKU we buy.
// All retail/competitor pricing displays use this list.
const SALES_GRADES = ["Regular", "Plus", "Premium", "Diesel"];
// Default Regular/Premium ratio for blending Plus. 50/50 produces 90 octane
// from typical 87/93 rack inputs. Real chains tune this per-store. Each
// store's blendRatio.regular fraction (0.0–1.0) overrides this default.
const PLUS_BLEND_DEFAULT = { regular: 0.50, premium: 0.50 };

//  TERRITORY ZONES 
// Terminals grouped into geographic zones for procurement management.
// Multiple terminals can share a zone. Zones provide the higher-level
// reporting view; territory enforcement in Plan stays at terminal level.
const ZONES = [
  { id:1, name:"Triangle / Eastern Carolinas", short:"Zone 1", terminals:["selma","apex"],                 color:"#3E6387" },
  { id:2, name:"Western Carolinas",            short:"Zone 2", terminals:["charlotte"],                    color:"#0D9488" },
  { id:3, name:"Virginia",                     short:"Zone 3", terminals:["richmond"],                     color:"#7C3AED" },
  { id:4, name:"Georgia",                      short:"Zone 4", terminals:["atlanta","macon","bainbridge"],  color:"#059669" },
  { id:5, name:"Alabama",                      short:"Zone 5", terminals:["birmingham"],                   color:"#EA580C" },
  { id:6, name:"Florida",                      short:"Zone 6", terminals:["jacksonville","tampa"],         color:"#0891B2" },
];
// Quick lookup: terminal id → zone
const TERMINAL_ZONE = {};
ZONES.forEach(z => z.terminals.forEach(tid => TERMINAL_ZONE[tid] = z));
// One color per terminal — derived from zone color, accessible to all map components
const TERMINAL_COLORS = Object.fromEntries(
  TERMINALS.map(t => [t.id, TERMINAL_ZONE[t.id]?.color || "#888"])
);

//  COLONIAL PIPELINE DATA 
// Colonial Pipeline runs ~5,500 miles Houston → NY Harbor — the primary supply
// artery for all SE terminals. Line 1 = gasoline/products, Line 2 = distillates.
// Cycle schedule: roughly 10-day cycles per product at each terminal.
const COLONIAL = {
  status: "NORMAL",          // NORMAL | ALLOCATED | CONSTRAINED | OUTAGE
  line1Capacity: 98.2,       // % of rated capacity (gasoline)
  line2Capacity: 94.7,       // % of rated capacity (distillates/diesel)
  allocationPct: null,       // null = no allocation; number = % of nominated volume approved
  cycleDay: 6,               // current day within 10-day cycle
  cycleDays: 10,
  nextCycleStart: "Apr 26",
  lastUpdated: "Apr 26, 08:15 CT",
  nominationDeadline: "Apr 25, 14:00 CT",
  segments: [
    { id:"houston_baton_rouge", name:"Houston → Baton Rouge",  miles:270,  status:"NORMAL",      flow:99.1 },
    { id:"baton_rouge_atlanta", name:"Baton Rouge → Atlanta",  miles:583,  status:"NORMAL",      flow:98.4 },
    { id:"atlanta_charlotte",   name:"Atlanta → Charlotte",    miles:323,  status:"NORMAL",      flow:97.8 },
    { id:"charlotte_richmond",  name:"Charlotte → Richmond",   miles:349,  status:"NORMAL",      flow:98.6 },
    { id:"richmond_nyharbor",   name:"Richmond → NY Harbor",   miles:354,  status:"NORMAL",      flow:96.2 },
    { id:"colonial_to_jax",     name:"Plantation: Atlanta → Jacksonville", miles:510, status:"NORMAL", flow:94.7 },
    { id:"jax_to_tampa",        name:"Plantation: Jacksonville → Tampa",   miles:250, status:"NORMAL", flow:95.1 },
  ],
  // Terminal-level cycle windows (days remaining until next scheduled lift window)
  terminalWindows: {
    selma:       { daysToWindow:2,  windowLen:3, grade:"All" },
    charlotte:   { daysToWindow:0,  windowLen:3, grade:"All" },  // window open NOW
    richmond:    { daysToWindow:4,  windowLen:3, grade:"All" },
    atlanta:     { daysToWindow:1,  windowLen:3, grade:"All" },
    jacksonville:{ daysToWindow:3,  windowLen:3, grade:"All" },
    tampa:       { daysToWindow:5,  windowLen:3, grade:"All" },
  },
  tariffs: {
    // $/gal from origin to each terminal (approximate Colonial tariff)
    selma:       { gasoline:0.0312, distillate:0.0334 },
    charlotte:   { gasoline:0.0289, distillate:0.0301 },
    richmond:    { gasoline:0.0356, distillate:0.0378 },
    atlanta:     { gasoline:0.0267, distillate:0.0289 },
    jacksonville:{ gasoline:0.0298, distillate:0.0321 },
    tampa:       { gasoline:0.0321, distillate:0.0345 },
  },
  recentEvents: [
    { date:"Apr 16", type:"info",  msg:"Line 1 resumed full flow after scheduled maintenance at Baton Rouge pump station" },
    { date:"Apr 16", type:"warn",  msg:"Line 2 temporary capacity reduction to 89% — Charlotte segment pump issue resolved Apr 11" },
    { date:"Apr 07", type:"info",  msg:"Colonial issued allocation notice for Apr 5–7 cycle: 97% of nominated volumes approved" },
    { date:"Apr 17", type:"info",  msg:"RVP switchover complete — summer-grade CBOB now flowing through entire system" },
  ],
};

// Derive spot availability flag: if allocation active or capacity <95%, spot harder to source
const SPOT_CONSTRAINED = COLONIAL.line1Capacity < 95 || COLONIAL.allocationPct !== null;
// Simulated rack prices ($/gal) — updated daily in real deployment via OPIS
// Rack prices ($/gal) — wholesale at the terminal loading rack, pre-freight,
// pre-tax. Grounded in EIA weekly retail data (week ending 03/23/26) for
// PADD 1C (Lower Atlantic) and PADD 3 (Gulf Coast), backing out federal
// excise ($0.184/gal gasoline, $0.244/gal diesel), average SE state taxes
// ($0.32/$0.32), retail margin ($0.18), and terminal-to-pump freight.
// Terminal basis differentials reflect Colonial Pipeline distance and
// regional supply dynamics (Richmond is end-of-line, FL is barge-dependent).
// Diesel currently trades at ~$1.55/gal premium to Regular due to elevated
// distillate cracks in 2026. Refresh quarterly or when market regime shifts.
const RACK_PRICES = {
  selma:       { Regular: 3.0012, Premium: 3.2512, Diesel: 4.5623 },
  apex:        { Regular: 2.9945, Premium: 3.2445, Diesel: 4.5556 },
  charlotte:   { Regular: 2.9834, Premium: 3.2334, Diesel: 4.5445 },
  richmond:    { Regular: 3.0334, Premium: 3.2834, Diesel: 4.5945 },
  atlanta:     { Regular: 2.9912, Premium: 3.2412, Diesel: 4.5523 },
  macon:       { Regular: 3.0089, Premium: 3.2589, Diesel: 4.5701 },
  bainbridge:  { Regular: 3.0234, Premium: 3.2734, Diesel: 4.5845 },
  birmingham:  { Regular: 2.9756, Premium: 3.2256, Diesel: 4.5367 },
  jacksonville:{ Regular: 3.0534, Premium: 3.3034, Diesel: 4.6134 },
  tampa:       { Regular: 3.0312, Premium: 3.2812, Diesel: 4.5923 },
};

const CONTRACT_DIFF = {
  selma:       { Regular: 0.0412, Premium: 0.0412, Diesel: 0.0523 },
  apex:        { Regular: 0.0395, Premium: 0.0395, Diesel: 0.0507 },
  charlotte:   { Regular: 0.0389, Premium: 0.0389, Diesel: 0.0501 },
  richmond:    { Regular: 0.0445, Premium: 0.0445, Diesel: 0.0556 },
  atlanta:     { Regular: 0.0367, Premium: 0.0367, Diesel: 0.0478 },
  macon:       { Regular: 0.0402, Premium: 0.0402, Diesel: 0.0514 },
  bainbridge:  { Regular: 0.0418, Premium: 0.0418, Diesel: 0.0529 },
  birmingham:  { Regular: 0.0378, Premium: 0.0378, Diesel: 0.0489 },
  jacksonville:{ Regular: 0.0423, Premium: 0.0423, Diesel: 0.0534 },
  tampa:       { Regular: 0.0401, Premium: 0.0401, Diesel: 0.0512 },
};

// ─── TERMINAL_SUPPLIERS — supplier-terminal pricing grain ────────────────────
// This is the *supplier-at-terminal* granular view used by the Plan optimizer
// and Today's Best Buy. Each row is one company's pricing + contract terms at
// one specific terminal. A company like Valero appears 3x if it supplies 3
// terminals, each with its own rack offset, differential, and commitment.
//
// This is distinct from the existing top-level SUPPLIERS roster (defined
// further down in the Procurement module) which is a company-level record
// with contacts, YTD totals, and a terminals[] list. That roster is for
// supplier relationship management; this table is for daily pricing decisions.
//
// Contract status:
//   "primary"   — main supplier, biggest commitment, deepest discount
//   "secondary" — backup contract, smaller commitment, competitive pricing
//   "spot-only" — no contract, lift at rack + small spot premium, used as
//                 a price check or during primary's allocation events
//
// In production this table would come from the chain's ERP/contract system.
const TERMINAL_SUPPLIERS = [
  // SELMA — 3 suppliers
  {
    id:"vlo-selma", name:"Valero Energy", short:"VLO", terminalId:"selma",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 }, // baseline
    contractDiff:{ Regular:  0.0412, Premium:  0.0412, Diesel:  0.0523 },
    monthlyCommit: 2_400_000, liftedMTD: 1_560_000, // 70% through month
    paymentTerms:"Net 10", rating:4.7, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Prime rack access, preferred shipper status",
  },
  {
    id:"shell-selma", name:"Shell Oil", short:"SHL", terminalId:"selma",
    contractStatus:"secondary",
    rackOffset:  { Regular: -0.0023, Premium: -0.0018, Diesel: -0.0031 },
    contractDiff:{ Regular:  0.0445, Premium:  0.0445, Diesel:  0.0555 },
    monthlyCommit: 800_000,   liftedMTD: 590_000,
    paymentTerms:"Net 15", rating:4.3, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Jun 30 2026", notes:"Backup supplier, quality controls strong",
  },
  {
    id:"marathon-selma", name:"Marathon Petroleum", short:"MPC", terminalId:"selma",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0041, Premium: -0.0029, Diesel: -0.0048 },
    contractDiff:{ Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    spotPremium: { Regular:  0.0089, Premium:  0.0089, Diesel:  0.0112 },
    monthlyCommit: 0, liftedMTD: 220_000,
    paymentTerms:"Prepay", rating:3.9, reliability:"moderate", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot only — no guaranteed allocation",
  },

  // APEX — 3 suppliers (Colonial terminal near RTP, NC)
  {
    id:"mpc-apex", name:"Marathon Petroleum", short:"MPC", terminalId:"apex",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0395, Premium:  0.0395, Diesel:  0.0507 },
    monthlyCommit: 1_800_000, liftedMTD: 1_310_000,
    paymentTerms:"Net 10", rating:4.8, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Primary APX supplier — strong Colonial access via L1",
  },
  {
    id:"vlo-apex", name:"Valero Energy", short:"VLO", terminalId:"apex",
    contractStatus:"secondary",
    rackOffset:  { Regular:  0.0010, Premium:  0.0008, Diesel:  0.0014 },
    contractDiff:{ Regular:  0.0415, Premium:  0.0415, Diesel:  0.0525 },
    monthlyCommit: 600_000, liftedMTD: 440_000,
    paymentTerms:"Net 10", rating:4.5, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Secondary — competitive on diesel",
  },
  {
    id:"citgo-apex", name:"Citgo Petroleum", short:"CITGO", terminalId:"apex",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0028, Premium: -0.0022, Diesel: -0.0035 },
    contractDiff:{ Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    spotPremium: { Regular:  0.0078, Premium:  0.0078, Diesel:  0.0095 },
    monthlyCommit: 0, liftedMTD: 85_000,
    paymentTerms:"Prepay", rating:4.1, reliability:"high", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot access — frequently competitive on Regular",
  },

  // MACON — 3 suppliers (Colonial terminal, central GA)
  {
    id:"mpc-macon", name:"Marathon Petroleum", short:"MPC", terminalId:"macon",
    contractStatus:"primary",
    rackOffset:  { Regular: 0.0000, Premium: 0.0000, Diesel: 0.0000 },
    contractDiff:{ Regular: 0.0402, Premium: 0.0402, Diesel: 0.0514 },
    monthlyCommit: 1_400_000, liftedMTD: 1_020_000,
    paymentTerms:"Net 10", rating:4.7, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Primary MCN supplier — solid Colonial allocation",
  },
  {
    id:"vlo-macon", name:"Valero Energy", short:"VLO", terminalId:"macon",
    contractStatus:"secondary",
    rackOffset:  { Regular: 0.0015, Premium: 0.0012, Diesel: 0.0019 },
    contractDiff:{ Regular: 0.0420, Premium: 0.0420, Diesel: 0.0535 },
    monthlyCommit: 500_000, liftedMTD: 365_000,
    paymentTerms:"Net 10", rating:4.4, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Secondary backup — good diesel position",
  },
  {
    id:"citgo-macon", name:"Citgo Petroleum", short:"CITGO", terminalId:"macon",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0022, Premium: -0.0018, Diesel: -0.0028 },
    contractDiff:{ Regular: 0.0000, Premium: 0.0000, Diesel: 0.0000 },
    spotPremium: { Regular: 0.0082, Premium: 0.0082, Diesel: 0.0099 },
    monthlyCommit: 0, liftedMTD: 65_000,
    paymentTerms:"Prepay", rating:4.0, reliability:"high", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot access — competitive on Regular mid-month",
  },

  // BAINBRIDGE — 2 suppliers (Plantation terminal, SW Georgia)
  {
    id:"citgo-bainbridge", name:"Citgo Petroleum", short:"CITGO", terminalId:"bainbridge",
    contractStatus:"primary",
    rackOffset:  { Regular: 0.0000, Premium: 0.0000, Diesel: 0.0000 },
    contractDiff:{ Regular: 0.0418, Premium: 0.0418, Diesel: 0.0529 },
    monthlyCommit: 900_000, liftedMTD: 645_000,
    paymentTerms:"Net 7", rating:4.3, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Jun 30 2026", notes:"Primary BNG — Plantation access strong on distillates",
  },
  {
    id:"mpc-bainbridge", name:"Marathon Petroleum", short:"MPC", terminalId:"bainbridge",
    contractStatus:"secondary",
    rackOffset:  { Regular: 0.0012, Premium: 0.0010, Diesel: 0.0016 },
    contractDiff:{ Regular: 0.0430, Premium: 0.0430, Diesel: 0.0542 },
    monthlyCommit: 350_000, liftedMTD: 255_000,
    paymentTerms:"Net 10", rating:4.5, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Secondary backup",
  },

  // BIRMINGHAM — 3 suppliers (Colonial terminal, central Alabama)
  {
    id:"mpc-birmingham", name:"Marathon Petroleum", short:"MPC", terminalId:"birmingham",
    contractStatus:"primary",
    rackOffset:  { Regular: 0.0000, Premium: 0.0000, Diesel: 0.0000 },
    contractDiff:{ Regular: 0.0378, Premium: 0.0378, Diesel: 0.0489 },
    monthlyCommit: 2_000_000, liftedMTD: 1_450_000,
    paymentTerms:"Net 10", rating:4.8, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Primary BHM — largest Colonial terminal in AL, excellent access",
  },
  {
    id:"vlo-birmingham", name:"Valero Energy", short:"VLO", terminalId:"birmingham",
    contractStatus:"secondary",
    rackOffset:  { Regular: 0.0008, Premium: 0.0006, Diesel: 0.0011 },
    contractDiff:{ Regular: 0.0395, Premium: 0.0395, Diesel: 0.0505 },
    monthlyCommit: 700_000, liftedMTD: 510_000,
    paymentTerms:"Net 10", rating:4.5, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Secondary — competitive on Premium",
  },
  {
    id:"shell-birmingham", name:"Shell Oil", short:"SHL", terminalId:"birmingham",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0019, Premium: -0.0014, Diesel: -0.0024 },
    contractDiff:{ Regular: 0.0000, Premium: 0.0000, Diesel: 0.0000 },
    spotPremium: { Regular: 0.0075, Premium: 0.0075, Diesel: 0.0092 },
    monthlyCommit: 0, liftedMTD: 95_000,
    paymentTerms:"Prepay", rating:4.2, reliability:"high", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot access — frequently under contract on diesel",
  },

  // CHARLOTTE — 3 suppliers
  {
    id:"shell-charlotte", name:"Shell Oil", short:"SHL", terminalId:"charlotte",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0389, Premium:  0.0389, Diesel:  0.0501 },
    monthlyCommit: 2_100_000, liftedMTD: 1_230_000,
    paymentTerms:"Net 10", rating:4.6, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Primary CLT supplier since 2019",
  },
  {
    id:"vlo-charlotte", name:"Valero Energy", short:"VLO", terminalId:"charlotte",
    contractStatus:"secondary",
    rackOffset:  { Regular:  0.0018, Premium:  0.0012, Diesel:  0.0025 },
    contractDiff:{ Regular:  0.0420, Premium:  0.0420, Diesel:  0.0540 },
    monthlyCommit: 700_000,   liftedMTD: 515_000,
    paymentTerms:"Net 15", rating:4.4, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Mar 31 2026", notes:"Tertiary coverage, renews Q1",
  },
  {
    id:"bp-charlotte", name:"BP Products", short:"BP", terminalId:"charlotte",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0034, Premium: -0.0026, Diesel: -0.0038 },
    contractDiff:{ Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    spotPremium: { Regular:  0.0078, Premium:  0.0078, Diesel:  0.0098 },
    monthlyCommit: 0, liftedMTD: 145_000,
    paymentTerms:"Prepay", rating:4.0, reliability:"moderate", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot buys during Shell allocation events",
  },

  // RICHMOND — 2 suppliers
  {
    id:"xom-richmond", name:"ExxonMobil", short:"XOM", terminalId:"richmond",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0445, Premium:  0.0445, Diesel:  0.0556 },
    monthlyCommit: 1_600_000, liftedMTD: 1_020_000,
    paymentTerms:"Net 10", rating:4.8, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Exclusive RIC contract, 10-year relationship",
  },
  {
    id:"marathon-richmond", name:"Marathon Petroleum", short:"MPC", terminalId:"richmond",
    contractStatus:"secondary",
    rackOffset:  { Regular: -0.0012, Premium: -0.0009, Diesel: -0.0018 },
    contractDiff:{ Regular:  0.0478, Premium:  0.0478, Diesel:  0.0592 },
    monthlyCommit: 500_000,   liftedMTD: 400_000,
    paymentTerms:"Net 15", rating:4.2, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Sep 30 2026", notes:"Small backup contract",
  },

  // ATLANTA — 3 suppliers
  {
    id:"vlo-atlanta", name:"Valero Energy", short:"VLO", terminalId:"atlanta",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0367, Premium:  0.0367, Diesel:  0.0478 },
    monthlyCommit: 1_900_000, liftedMTD: 1_520_000,
    paymentTerms:"Net 10", rating:4.6, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Largest diff-negotiated contract",
  },
  {
    id:"citgo-atlanta", name:"Citgo Petroleum", short:"CITGO", terminalId:"atlanta",
    contractStatus:"secondary",
    rackOffset:  { Regular: -0.0021, Premium: -0.0015, Diesel: -0.0029 },
    contractDiff:{ Regular:  0.0398, Premium:  0.0398, Diesel:  0.0512 },
    monthlyCommit: 650_000,   liftedMTD: 470_000,
    paymentTerms:"Net 15", rating:4.1, reliability:"moderate", allocationStatus:"normal",
    contractExpiry:"Jun 30 2026", notes:"Secondary, renews mid-year",
  },
  {
    id:"marathon-atlanta", name:"Marathon Petroleum", short:"MPC", terminalId:"atlanta",
    contractStatus:"spot-only",
    rackOffset:  { Regular: -0.0044, Premium: -0.0033, Diesel: -0.0051 },
    contractDiff:{ Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    spotPremium: { Regular:  0.0092, Premium:  0.0092, Diesel:  0.0115 },
    monthlyCommit: 0, liftedMTD: 180_000,
    paymentTerms:"Prepay", rating:3.8, reliability:"moderate", allocationStatus:"normal",
    contractExpiry:null, notes:"Spot arb when ATL rack swings low",
  },

  // JACKSONVILLE — 2 suppliers
  {
    id:"marathon-jax", name:"Marathon Petroleum", short:"MPC", terminalId:"jacksonville",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0423, Premium:  0.0423, Diesel:  0.0534 },
    monthlyCommit: 1_400_000, liftedMTD: 905_000,
    paymentTerms:"Net 10", rating:4.5, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Marine-delivered, hurricane exposure",
  },
  {
    id:"vlo-jax", name:"Valero Energy", short:"VLO", terminalId:"jacksonville",
    contractStatus:"secondary",
    rackOffset:  { Regular:  0.0029, Premium:  0.0021, Diesel:  0.0036 },
    contractDiff:{ Regular:  0.0456, Premium:  0.0456, Diesel:  0.0572 },
    monthlyCommit: 450_000,   liftedMTD: 335_000,
    paymentTerms:"Net 15", rating:4.3, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Sep 30 2026", notes:"Redundancy for hurricane season",
  },

  // TAMPA — 2 suppliers
  {
    id:"citgo-tampa", name:"Citgo Petroleum", short:"CITGO", terminalId:"tampa",
    contractStatus:"primary",
    rackOffset:  { Regular:  0.0000, Premium:  0.0000, Diesel:  0.0000 },
    contractDiff:{ Regular:  0.0401, Premium:  0.0401, Diesel:  0.0512 },
    monthlyCommit: 1_100_000, liftedMTD: 810_000,
    paymentTerms:"Net 10", rating:4.4, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Dec 31 2026", notes:"Primary TPA supplier",
  },
  {
    id:"marathon-tampa", name:"Marathon Petroleum", short:"MPC", terminalId:"tampa",
    contractStatus:"secondary",
    rackOffset:  { Regular: -0.0019, Premium: -0.0014, Diesel: -0.0026 },
    contractDiff:{ Regular:  0.0434, Premium:  0.0434, Diesel:  0.0548 },
    monthlyCommit: 350_000,   liftedMTD: 260_000,
    paymentTerms:"Net 15", rating:4.2, reliability:"high", allocationStatus:"normal",
    contractExpiry:"Mar 31 2026", notes:"Small backup contract",
  },
];

// Helper: list all supplier-terminal instances for a given terminal
const SUPPLIERS_BY_TERMINAL = {};
TERMINAL_SUPPLIERS.forEach(s => {
  (SUPPLIERS_BY_TERMINAL[s.terminalId] = SUPPLIERS_BY_TERMINAL[s.terminalId] || []).push(s);
});

// Compute a supplier's landed-cost-per-gallon contribution (rack + diff or
// spot premium, depending on contract status). Does NOT include freight or
// tax — those are store/route dependent and added by callers.
function supplierCostPerGal(supplier, grade) {
  const termRack = RACK_PRICES[supplier.terminalId]?.[grade] || 0;
  const rack = termRack + (supplier.rackOffset?.[grade] || 0);
  if (supplier.contractStatus === "spot-only") {
    return {
      rack,
      premium: supplier.spotPremium?.[grade] || 0,
      total: rack + (supplier.spotPremium?.[grade] || 0),
      isSpot: true,
    };
  }
  return {
    rack,
    diff: supplier.contractDiff?.[grade] || 0,
    total: rack + (supplier.contractDiff?.[grade] || 0),
    isSpot: false,
  };
}

// ─── SUPPLIER BRANDING — brand colors + stylized mini-logos ────────────────
// Each supplier gets a recognizable mini-logo built from compact SVG
// primitives. The `primary` color drives the supplier's short-code pill;
// `accent` is used for the logo's secondary elements.
// Opportune brand mark — displayed in top bar
const OPPORTUNE_LOGO = "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAwAAAAgCAYAAAAmG5mqAAABCGlDQ1BJQ0MgUHJvZmlsZQAAeJxjYGA8wQAELAYMDLl5JUVB7k4KEZFRCuwPGBiBEAwSk4sLGHADoKpv1yBqL+viUYcLcKakFicD6Q9ArFIEtBxopAiQLZIOYWuA2EkQtg2IXV5SUAJkB4DYRSFBzkB2CpCtkY7ETkJiJxcUgdT3ANk2uTmlyQh3M/Ck5oUGA2kOIJZhKGYIYnBncAL5H6IkfxEDg8VXBgbmCQixpJkMDNtbGRgkbiHEVBYwMPC3MDBsO48QQ4RJQWJRIliIBYiZ0tIYGD4tZ2DgjWRgEL7AwMAVDQsIHG5TALvNnSEfCNMZchhSgSKeDHkMyQx6QJYRgwGDIYMZAKbWPz9HbOBQAAAEDklEQVR42n2Uf0jcdRjHn+fz+X7vTu/O2SnNPOaWkVBRwTRY0LAbs2H+KAwdIRUFadCK1QYjYp33T/RPRFsGJ+EfElknbAk2FwmXDELq7Adpqytn6s5zzi7vl9/7fj+fz/fpDzfR6Xr+fZ7Xh+f95v15AG5T0WC9BgBwobf5neEzLXcDABABsh2Ho/VaIDQuvwm3vFXs5D0rWZG72dsGxMK1eiAwLkc/bn21wlf8LhBkN/e3AOFwrV7XPSm+Otv8or/c9VEmbxEBge5QuA2IRNp5d/ekGD7b1H7vHm9/OmtdXCuofl1jHhK22gJQMMg6OobUaG9r077d7kg6J6aTq3qbxnCJM8Ysk9MGQASIoRANnGhwuxw4aFlq9q/ZTGPHiSGDiEpsm2AnDYRVnOscvf9mzZFnT48tEEU1YEzdasqGhoq7qhAQAUgAgA2IAanMnIWMQbG3jG3VQMT6evoMqYRw76q80zDEYcMQDd6K+3ZbhZwYPDm4RkTrEFGEAwDMxicOXOpvyS/9Okiba2V+Ui78+dPjNx7mAACQM8QTQpjm1PmXKPblyTHDEA3Z7OphU4gQEV0nIjudTjcDAMDKyrxfKfrHMteWJgaeMS+eOfT+ZpGLV6b3Sil/l1JmksnkPubxlJ9mDHxXZ357Pp/PWo7i0hIi4vH4h854PO6srH5gLpPJHOWce8vKyt5mmubotAG+r76/bsxV5PXYSgpEVInEOVVTU2MSEff5fL8opSYZY0cZ59wDADEiIsYQAOxbrUciQtu2Jznn3nWrbEDGGMH/FBEJAACmlFwFBnVExNZjsC3xhIjEOd+vlMozKdUgA3hkbubHQwUjm2Nc04mI+/1tPB6POxFRLS8v7+ecPyql/AJSiUSVIlq1zLXExEDbNluTs5f3SSlnpJTpVCq1V/P5/fOFgujUuDbs8ZZyraT64Zzx9RFppm2Xq+SA06m/ZttQZhj5Jp/PN7cRjcRM7LFL/S35a1Ofb4lGKvGzlZibPrgRDSJAImK1AHq0r8n6bvDloUJBNBaEaPzh3Buffhs+UugC0ImIbVwNRLRPhbuKNc2h51ILiy6XPurS9dH04lRSc3qcXZFTxYhob/kPmdUlm4iAa04HEWmADFB3IwCBTF6l254ZIpsjovzkveZKdxF/Wkk7P88te0eAMQREyAZfqHc9WOkYdRdp96wVVGfHsaEcBYMMEUi7Oex0WUjkklJBeeCgb8i3y/HQ5SuZztbjI8NEQYYYsgEANoA7dM6VTRlPkfZciceBf/ydeaX1+MhnsXCtjhgS21YSpkYIQKVeJy5cy7/Z/PpIOHbjEm5eW9sqGEoXr+dDTx4b+SAardfqAuNih9gCAgCc731qz2hvSw8AAEXaOQDgTjH/D3BWM35YxCKqAAAAAElFTkSuQmCC";

const SUPPLIER_BRANDS = {
  "Valero Energy":       { primary:"#00A651", accent:"#003F7F", text:"#FFFFFF" },
  "Shell Oil":           { primary:"#DD1D21", accent:"#FBCE07", text:"#FFFFFF" },
  "Marathon Petroleum":  { primary:"#003087", accent:"#E4002B", text:"#FFFFFF" },
  "ExxonMobil":          { primary:"#EC1C24", accent:"#FFFFFF", text:"#FFFFFF" },
  "Citgo Petroleum":     { primary:"#E31837", accent:"#F47B20", text:"#FFFFFF" },
  "BP Products":         { primary:"#009E3A", accent:"#FFE600", text:"#FFFFFF" },
  "Motiva":              { primary:"#5B8FA8", accent:"#4A7A90", text:"#FFFFFF" },
  "Gulf":                { primary:"#E8521A", accent:"#1C3B8C", text:"#FFFFFF" },
};


// Supplier name aliases — maps long database names to SUPPLIER_LOGOS keys
const SUPPLIER_NAME_MAP = {
  "Valero Marketing & Supply": "Valero Energy",
  "Shell Oil Products US":     "Shell Oil",
  "ExxonMobil Fuels & Lubricants": "ExxonMobil",
  "Motiva Enterprises":        "Motiva",
  "Gulf Oil LP":               "Gulf",
  "Sunoco LP":                 "Sunoco",
  "Citgo Petroleum":           "Citgo Petroleum",
  "BP Products":               "BP Products",
};
// ─── ZoneBadge — colored zone pill rendered anywhere a terminal appears ──────
// ─── SUPPLIER PERFORMANCE SCORE ──────────────────────────────────────────────
// Computed from real data — not hardcoded. Returns { total, breakdown } where
// breakdown is an array of { label, score, max, note } for the tooltip.
//
// Components:
//   Delivery Reliability  35pts — penalises incidents from DETENTION_LOG + OVERSHORT_LOG
//   Contract Adherence    25pts — avg MTD lift% across all terminal contracts
//   Credit Standing       15pts — YTD spend vs credit limit utilization
//   Pricing Competitiveness 15pts — tier and pricing basis advantage
//   Relationship / Tenure 10pts — tier, multi-terminal, contract length
function computeSupplierScore(s) {
  // ── Delivery Reliability (35) ─────────────────────────────────────────────
  // Start at 35. Deduct per incident from DETENTION_LOG (site-related) and
  // OVERSHORT_LOG (product variance). Cap deduction at 25 so floor is 10.
  const detentionHits = DETENTION_LOG.filter(d => {
    const store = d.site || "";
    return false; // detention is carrier-side, not supplier-side — no deduction
  }).length;
  const osHits = OVERSHORT_LOG.filter(d => {
    // Over/short BOL prefix maps to terminal, which maps to supplier
    const prefix = d.bol?.split("-")[0]?.toLowerCase();
    const termId = prefix === "sel" ? "selma" : prefix === "clt" ? "charlotte" :
                   prefix === "ric" ? "richmond" : prefix === "atl" ? "atlanta" :
                   prefix === "jax" ? "jacksonville" : prefix === "tpa" ? "tampa" :
                   prefix === "apx" ? "apex" : prefix === "mcn" ? "macon" :
                   prefix === "bng" ? "bainbridge" : prefix === "bhm" ? "birmingham" : null;
    if (!termId) return false;
    const ts = TERMINAL_SUPPLIERS.find(ts => ts.terminalId === termId &&
      ts.name.toLowerCase().includes(s.short.toLowerCase()));
    const isSevere = Math.abs(d.variance) > 50; // >50 gal variance
    return ts && isSevere;
  }).length;
  const incidentDeduction = Math.min(25, s.incidents * 8 + osHits * 4);
  const deliveryScore = 35 - incidentDeduction;
  const deliveryNote = s.incidents === 0 && osHits === 0
    ? "No incidents or O/S variances YTD"
    : `${s.incidents} incident${s.incidents !== 1?"s":""}, ${osHits} O/S variance${osHits !== 1?"s":""}`;

  // ── Contract Adherence (25) ───────────────────────────────────────────────
  // Average MTD lift % across all terminal contracts for this supplier.
  const contracts = TERMINAL_SUPPLIERS.filter(ts =>
    ts.name.toLowerCase().includes(s.short.toLowerCase()) && ts.monthlyCommit > 0
  );
  let adherenceScore = 20; // default if no contract data
  let adherenceNote = "No commitment contracts";
  if (contracts.length > 0) {
    const avgLift = contracts.reduce((sum, ts) => {
      const pct = ts.liftedMTD / ts.monthlyCommit * (30/22); // project to EOM
      return sum + Math.min(1.10, pct); // cap at 110% (overlifting hurts less)
    }, 0) / contracts.length;
    adherenceScore = Math.round(Math.min(25, avgLift * 25));
    adherenceNote = `Projected EOM lift: ${(avgLift*100).toFixed(0)}% of commit (${contracts.length} contract${contracts.length>1?"s":""})`;
  }

  // ── Credit Standing (15) ──────────────────────────────────────────────────
  // YTD spend vs credit limit. 100% utilization = 5pts, 50% = 15pts, 0% = 10pts
  const utilization = s.creditLimit > 0 ? s.ytdSpend / (s.creditLimit * 12) : 0;
  const creditScore = utilization > 0.90 ? 5 :
                      utilization > 0.75 ? 9 :
                      utilization > 0.50 ? 12 : 15;
  const creditNote = `YTD spend $${(s.ytdSpend/1e6).toFixed(1)}M vs $${(s.creditLimit/1e6).toFixed(1)}M limit (${(utilization*100).toFixed(0)}% utilization)`;

  // ── Pricing Competitiveness (15) ──────────────────────────────────────────
  // Tier 1 direct refiner gets full points. Jobbers and spot-only get fewer.
  const pricingScore = s.tier === 1 ? 15 : s.tier === 2 ? 10 : 6;
  const pricingNote = s.tier === 1 ? "Direct refiner — OPIS rack pricing"
                    : s.tier === 2 ? "Jobber — posted price + margin"
                    : "Spot-only — no contract pricing advantage";

  // ── Relationship / Tenure (10) ────────────────────────────────────────────
  // Multi-terminal + long contract + volume = full points
  const tenureScore = Math.min(10,
    (s.terminals.length >= 3 ? 5 : s.terminals.length >= 2 ? 3 : 2) +
    (s.contractType === "Annual Volume" ? 3 : 1) +
    (s.ytdVolume > 5_000_000 ? 2 : s.ytdVolume > 2_000_000 ? 1 : 0)
  );
  const tenureNote = `${s.terminals.length} terminal${s.terminals.length>1?"s":""}  · ${s.contractType} · ${(s.ytdVolume/1e6).toFixed(1)}M gal YTD`;

  const total = Math.max(0, Math.min(100, deliveryScore + adherenceScore + creditScore + pricingScore + tenureScore));

  return {
    total,
    breakdown: [
      { label:"Delivery Reliability", score:deliveryScore,  max:35, note:deliveryNote  },
      { label:"Contract Adherence",   score:adherenceScore, max:25, note:adherenceNote },
      { label:"Credit Standing",      score:creditScore,    max:15, note:creditNote    },
      { label:"Pricing",              score:pricingScore,   max:15, note:pricingNote   },
      { label:"Relationship",         score:tenureScore,    max:10, note:tenureNote    },
    ],
  };
}

function ZoneBadge({ terminalId, size = "sm" }) {
  const zone = TERMINAL_ZONE[terminalId];
  if (!zone) return null;
  const pad   = size === "lg" ? "2px 8px" : "1px 5px";
  const fsize = size === "lg" ? 10 : 8;
  return (
    <span style={{
      fontSize:fsize, fontWeight:800, padding:pad, borderRadius:3,
      background:zone.color, color:"#fff", letterSpacing:.3,
      fontFamily:"Arial,sans-serif", flexShrink:0, whiteSpace:"nowrap",
    }}>
      Z{zone.id}
    </span>
  );
}

function supplierBrand(supplierName) {
  return SUPPLIER_BRANDS[supplierName] || { primary:"#64748B", accent:"#94A3B8", text:"#FFFFFF" };
}

const SUPPLIER_LOGOS = {
  "Shell Oil": "data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIyNTAwIiBoZWlnaHQ9IjI1MDAiIHZpZXdCb3g9IjAgMCAxOTIuNzU2IDE5Mi43NTYiPjxwYXRoIGZpbGwtcnVsZT0iZXZlbm9kZCIgY2xpcC1ydWxlPSJldmVub2RkIiBmaWxsPSIjZmZmIiBkPSJNMCAwaDE5Mi43NTZ2MTkyLjc1NkgwVjB6Ii8+PHBhdGggZD0iTTE2OS4yNDQgNTMuNzNhODguNjQyIDg4LjY0MiAwIDAgMSA4LjAyOSAxNC44NzNjMCAuMDAxLjAwMi0uMDAyLjAwNC0uMDAxYTg1Ljc4MiA4NS43ODIgMCAwIDEgNS4yMjEgMTYuNjc1IDg3LjQwNiA4Ny40MDYgMCAwIDEgMS43NTQgMTcuNDkzIDg3LjAyIDg3LjAyIDAgMCAxLS40NTUgOC43NDYgMTAxLjM5OCAxMDEuMzk4IDAgMCAxLTEuMzAzIDguODczbC0uMjAzIDEuMDYyLTI2LjA2NiAxOC44NzktNC4yMTcgMzMuNTMzaC00NC45NzFsLTEuNjM1IDEuMDlhMTMuOTc0IDEzLjk3NCAwIDAgMS00LjE4OSAyLjIyOWgtLjAxYy0xLjUzMS41MDQtMy4xMzkuNzQ2LTQuODI1Ljc0Ni0xLjcyMSAwLTMuMzI3LS4yNDItNC44NTctLjc0NmgtLjAxMWMtMS40NjgtLjQ4Mi0yLjg0MS0xLjIwNy00LjE1Ni0yLjE4NmwtMS44NC0xLjEzM0g0MC45NThsLTQuMjg0LTMzLjUyNy0yNi4yMDItMTguODg1LS4yMTEtMS4wNDFhODguMTk3IDg4LjE5NyAwIDAgMS0xLjMyNi04LjkwNiA4OS4zNzkgODkuMzc5IDAgMCAxLS40MzEtOC43MzRjMC01LjkyLjU3Ny0xMS43NDIgMS43MjgtMTcuNDQ0YTg3LjE4IDg3LjE4IDAgMCAxIDUuMTgyLTE2LjcxMyA4OC44NjIgODguODYyIDAgMCAxIDguMDI5LTE0LjkxMiA4Ni44NSA4Ni44NSAwIDAgMSAxMC43NjktMTMuMDk5IDg3LjM5MSA4Ny4zOTEgMCAwIDEgMTMuMDE3LTEwLjcxMSA4OS40NDIgODkuNDQyIDAgMCAxIDE0LjkxNy04LjA4N2M1LjQ5Ni0yLjM0IDExLjA4Mi00LjA4NiAxNi43NzItNS4yNDJhODcuNDEgODcuNDEgMCAwIDEgMTcuNDYtMS43MzNjNS45MDMgMCAxMS43MzcuNTgyIDE3LjQ5MyAxLjc1M2E4Ni44MjcgODYuODI3IDAgMCAxIDE2Ljc0IDUuMjIyIDg4LjQ4NCA4OC40ODQgMCAwIDEgMTQuODU1IDguMDYxYzQuNjU2IDMuMTQxIDkgNi43MjIgMTMuMDEyIDEwLjczNy4wMDQuMDAyLS4wMDIuMDA4IDAgLjAxYTg5LjQxNCA4OS40MTQgMCAwIDEgMTAuNzY2IDEzLjExOHoiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJNMTc0Ljc3IDY5LjY2OGMtNC4zMjYtMTAuMjI1LTEwLjQyMi0xOS4yNzEtMTguMjIxLTI3LjEzNi03LjgwMS03LjgtMTYuODQ2LTEzLjg5Ni0yNy4wMDYtMTguMjIyLTEwLjYxNy00LjUyMi0yMS42OTUtNi43NTEtMzMuMTY1LTYuNzUxLTExLjUzNiAwLTIyLjU0NyAyLjIyOS0zMy4xNjYgNi43NTEtMTAuMTYgNC4zMjYtMTkuMjcxIDEwLjQyMi0yNy4wNyAxOC4yMjItNy44NjUgNy44NjUtMTMuODk2IDE2LjkxMS0xOC4yMjIgMjcuMTM2LTQuNDU3IDEwLjU1My02LjY4NSAyMS42My02LjY4NSAzMy4xMDEgMCA1LjYzNy41MjQgMTEuMjczIDEuNzA0IDE3LjEwN2wyNi4yODMgMTguOTQxIDQuMTI5IDMyLjMxNGg0Mi45MzJsMi41NTYgMS41NzJjMi4yMjkgMS43MDUgNC42NTQgMi40OSA3LjUzOCAyLjQ5IDIuODE5IDAgNS4zMS0uNzg1IDcuNDcyLTIuNDlsMi4zNTktMS41NzJIMTQ5LjZsNC4wNjQtMzIuMzE0IDI2LjE1Mi0xOC45NDFjMS4xMTUtNS44MzQgMS43MDUtMTEuNDcxIDEuNzA1LTE3LjEwNyAwLTExLjQ3MS0yLjIyOC0yMi41NDgtNi43NTEtMzMuMTAxeiIgZmlsbC1ydWxlPSJldmVub2RkIiBjbGlwLXJ1bGU9ImV2ZW5vZGQiIGZpbGw9IiNjYzIyMjkiLz48cGF0aCBkPSJNMTYyLjE4NiA3OS4zNjljLTEuNzA1LTcuMjEtNS4zNzUtMTMuMzcyLTExLjA3OC0xOC4zNTNsLTM5LjkxNiA2OC43NTcgMzUuMzI4LTc1LjM3N2MtNC43MTktNi4yMjctMTAuNjg0LTEwLjQ4Ny0xOC4yMjEtMTIuOTEzbC0yNC40NDkgODUuNDcxIDE3Ljg5NS04OC45NDVjLTUuNTcyLTMuMDgxLTExLjQ3MS00LjY1NC0xNy43NjQtNC42NTRsLTMuOTk4LjI2Mi0zLjUzOSA5Mi41NDktMy43MzYtOTIuNTQ5LTMuOTMzLS4yNjJjLTYuMjkyIDAtMTIuMjU3IDEuNTczLTE3Ljc2MyA0LjY1NGwxNy42OTcgODguOTQ1LTI0LjI1MS04NS40N0M1Ni45MiA0My45MSA1MC44MjUgNDguMTcgNDYuMjM3IDU0LjM5N2wzNS41MjUgNzUuMzc3LTQwLjExNC02OC43NTdjLTUuNzAyIDQuOTgxLTkuMzczIDExLjE0My0xMS4wNzcgMTguMzUzbDQ0LjcwMiA1NC45MjYtNDYuMDEzLTQ2LjIxYy0yLjA5OCA0LjcyLTMuMTQ2IDkuNjM2LTMuMTQ2IDE0LjY4MyAwIDIuODE4LjMyOCA1LjgzMiAxLjExNCA5LjA0NWwyNS44MjUgMTguODc3IDMuNDA5IDI1LjM2NWgzMS4zOTZsNC40NTcgMy40MDhjMS4yNDYuODUyIDIuNTU3IDEuMjQ2IDQuMDY0IDEuMzExIDEuNDQyLS4wNjQgMi44MTktLjQ1OSAzLjkzMy0xLjMxMWw0LjcxOS0zLjQwOGgzMS41MjdsMy4yMTMtMjUuMzY1IDI1Ljc1OC0xOC44NzdjLjcyMS0zLjIxMyAxLjExNS02LjIyNyAxLjExNS05LjA0NSAwLTUuMDQ3LTEuMTE1LTkuOTYzLTMuMTQ2LTE0LjY4M2wtNDUuNzUgNDYuMjA4IDQ0LjQzOC01NC45MjV6IiBmaWxsLXJ1bGU9ImV2ZW5vZGQiIGNsaXAtcnVsZT0iZXZlbm9kZCIgZmlsbD0iI2Y2ZDMzMCIvPjwvc3ZnPg==",
  "Motiva": "data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIyNTAwIiBoZWlnaHQ9IjI1MDAiIHZpZXdCb3g9IjAgMCAxOTIuNzU2IDE5Mi43NTYiPjxnIGZpbGwtcnVsZT0iZXZlbm9kZCIgY2xpcC1ydWxlPSJldmVub2RkIj48cGF0aCBmaWxsPSIjZmZmIiBkPSJNMCAwaDE5Mi43NTZ2MTkyLjc1NkgwVjB6Ii8+PHBhdGggZmlsbD0iIzkzOWRhNyIgZD0iTTE1LjA4OCAxMTIuMDc4bC02LjU4NC0uNTA2Vjg5Ljc5NGgxMC4xMjlsNy41OTggMTQuMTgxIDcuNTk3LTE0LjE4MWgxMC42MzZ2MjEuNzc4SDM3Ljg4Vjk2LjM3OGwtOS4xMTcgMTUuMTk0aC01LjA2NWwtOC42MS0xNS4xOTR2MTUuN3pNODEuNDM3IDk1LjM2NWg5LjYyM3YxNi4yMDdoNi41ODVWOTQuODU5aDkuMTE3di01LjA2NUg4MS45NDNsLS41MDYgNS41NzF6TTgxLjQzNyA4MC42Nzd2Ni4wNzhoMjYuMzM2di02LjA3OEg4MS40Mzd6TTExMC44MTIgODkuNzk0djIxLjc3OGg2LjU4NFY4OS43OTRoLTYuNTg0ek0xMjEuNDQ5IDg5Ljc5NGwxMi4xNTUgMjEuNzc4aDguMTA1bDEyLjE1NC0yMS43NzhoLTcuNTk3bC04LjYxIDE1LjctOC42MDktMTUuN2gtNy41OTh6TTcxLjMwNyAxMDQuNDgyYzAgMS4wMTItMS4wMTMgMi4wMjUtMi4wMjYgMi4wMjVINTcuNjMyYy0xLjAxMyAwLTIuMDI2LTEuMDE0LTIuMDI2LTIuMDI1di02LjU4NGMwLTEuMDE0IDEuMDEzLTIuMDI3IDIuMDI2LTIuMDI3aDExLjY0OWMxLjAxMyAwIDIuMDI2IDEuMDEzIDIuMDI2IDIuMDI3djYuNTg0em03LjA5MS0xMC42MzZjMC0yLjUzMi0xLjUyLTQuMDUyLTMuNTQ1LTQuMDUySDUyLjU2OGMtMi4wMjYgMC0zLjU0NiAxLjUyLTMuNTQ2IDQuMDUydjE0LjE4MmMwIDIuMDI1IDEuNTIgNC4wNTEgMy41NDYgNC4wNTFoMjIuMjg1YzIuMDI2IDAgMy41NDUtMi4wMjUgMy41NDUtNC4wNTFWOTMuODQ2ek0xNTguOTI4IDExMS41NzJsMi4wMjctNC4wNTFoMTMuNjc0bDIuMDI1IDQuMDUxaDcuNTk4bC0xMi4xNTYtMjEuNzc4aC05LjExNWwtMTEuNjQ4IDIxLjc3OGg3LjU5NXptNC4wNTItOC42MDlsNC41NTktOC4xMDQgNC4wNTEgOC4xMDRoLTguNjF6Ii8+PC9nPjwvc3ZnPg==",
  "Marathon Petroleum": "data:image/svg+xml;base64,PHN2ZyBoZWlnaHQ9IjE4OTAiIHZpZXdCb3g9IjIuNTQ2IDMuNiA1MzIuNDk0IDM5OS45MjQiIHdpZHRoPSIyNTAwIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciPjxwYXRoIGQ9Im0zODUuNDIgMy42MDFjMjAuMjAyLjYwMyA0MC4xMDMgMTMuNDEzIDQ4LjExNSAzMi4zNjNsNDkuMjY1IDEwOS45NiAzOS4wNCA4Ny41NDRjMi43NDUgOC4zMTMgMi41ODYgMTguNTkzIDEuMDg3IDI3LjQ3NmwtMjguOTc1IDEwNy4wNjZjLTYuNTY4IDE4Ljc1MS0yNS44MDIgMzMuODU0LTQ1LjMwNyAzNS4zM2wtMzY3Ljg5LS4wNGMtMTkuMDc2LTEuMjE0LTM4LjI5NS0xNC40MTMtNDUuNDI2LTMyLjYxN2wtNC4wNDUtMTEuNzMtMTUuMjE0LTU1LjY4My0xMS43MzktNDIuODA4Yy0xLjc4NS05LjgyOC0uMzg5LTIwLjExNiAyLjY5Ny0yOC43ODVsODQuNDQyLTE5My42MjdjNy4yMzUtMTkuNTc2IDI3LjQwNi0zMy41NjggNDguMDI5LTM0LjQ1eiIgZmlsbD0iIzFlNTlhZSIvPjxwYXRoIGQ9Im0zODUuNDIgMy42MDFjMjAuMjAyLjYwMyA0MC4xMDMgMTMuNDEzIDQ4LjExNSAzMi4zNjNsNDkuMjY1IDEwOS45NiAzOS4wNCA4Ny41NDRjMi43NDUgOC4zMTMgMi41ODYgMTguNTkzIDEuMDg3IDI3LjQ3NmwtMjguOTc1IDEwNy4wNjZjLTYuNTY4IDE4Ljc1MS0yNS44MDIgMzMuODU0LTQ1LjMwNyAzNS4zM2wtMzY3Ljg5LS4wNGMtMTkuMDc2LTEuMjE0LTM4LjI5NS0xNC40MTMtNDUuNDI2LTMyLjYxN2wtNC4wNDUtMTEuNzMtMTUuMjE0LTU1LjY4My0xMS43MzktNDIuODA4Yy0xLjc4NS05LjgyOC0uMzg5LTIwLjExNiAyLjY5Ny0yOC43ODVsODQuNDQyLTE5My42MjdjNy4yMzUtMTkuNTc2IDI3LjQwNi0zMy41NjggNDguMDI5LTM0LjQ1eiIgZmlsbD0ibm9uZSIvPjxwYXRoIGQ9Im0zODcuMDI5IDIzLjAyMWMxMy4yNzggMS4wMjMgMjYuMjQ3IDEyLjA4OCAzMC4wNTQgMjQuNzI0bDc3LjUzNCAxNzIuMDljNC43NDQgOS43NjUgMTIuODc0IDIxLjUyIDkuNjg1IDM0LjY2M2wtNC4zMjMgMTcuNzQ0LTIzLjM5IDg2LjQ5Yy0zLjA1NSAxMi43NjItMTYuMTU4IDIzLjA1LTI4LjU4NyAyNS4xNTJsLTM2Mi44NTQuMDdjLTExLjU1Ni0uMjEzLTIxLjkzMS00LjYyMy0yOC45MzUtMTQuNDY3LTcuMDA0LTExLjUxNy0zMy40OC0xMTQuNDczLTMzLjQ4LTExNC40NzMtMS4yNy0xMC4wNTggMi43Ni0xOC44NjIgNi41ODMtMjcuMjQ2bDY1LjQ3LTE0OS41NDkgMTYuMDctMzYuNGM2LjYxNS0xMS44NzMgMTkuMTYzLTE4LjA3NiAzMS44MTUtMTguODN6IiBmaWxsPSIjZmZmIi8+PHBhdGggZD0ibTM4Ny4wMjkgMjMuMDIxYzEzLjI3OCAxLjAyMyAyNi4yNDcgMTIuMDg4IDMwLjA1NCAyNC43MjRsNzcuNTM0IDE3Mi4wOWM0Ljc0NCA5Ljc2NSAxMi44NzQgMjEuNTIgOS42ODUgMzQuNjYzbC00LjMyMyAxNy43NDQtMjMuMzkgODYuNDljLTMuMDU1IDEyLjc2Mi0xNi4xNTggMjMuMDUtMjguNTg3IDI1LjE1MmwtMzYyLjg1NC4wN2MtMTEuNTU2LS4yMTMtMjEuOTMxLTQuNjIzLTI4LjkzNS0xNC40NjctNy4wMDQtMTEuNTE3LTMzLjQ4LTExNC40NzMtMzMuNDgtMTE0LjQ3My0xLjI3LTEwLjA1OCAyLjc2LTE4Ljg2MiA2LjU4My0yNy4yNDZsNjUuNDctMTQ5LjU0OSAxNi4wNy0zNi40YzYuNjE1LTExLjg3MyAxOS4xNjMtMTguMDc2IDMxLjgxNS0xOC44M3oiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMjYzLjAzMSAxNzguMTI3IDQ1LjQ0Mi0xMTcuMTcgNjkuMDQ3LS4wMzIgNjEuMjgyIDE5OS42OTMtODQuNTM4LS4wMDgtOS40MTUtMTA5LjY0Mi01NC43ODYgMTA5LjY0Mi01My40OTMuMDY0LTU1LjQxMi0xMDguNzk0LTkuMDgyIDEwOC43My04NC4zOC4wNTYgNTkuMzk0LTE5OS42MzggNjkuMTktLjAzMnoiIGZpbGw9IiNlZDExNGMiLz48cGF0aCBkPSJtMjYzLjAzMSAxNzguMTI3IDQ1LjQ0Mi0xMTcuMTcgNjkuMDQ3LS4wMzIgNjEuMjgyIDE5OS42OTMtODQuNTM4LS4wMDgtOS40MTUtMTA5LjY0Mi01NC43ODYgMTA5LjY0Mi01My40OTMuMDY0LTU1LjQxMi0xMDguNzk0LTkuMDgyIDEwOC43My04NC4zOC4wNTYgNTkuMzk0LTE5OS42MzggNjkuMTktLjAzMnoiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMTAxLjAxNCAzMTQuMjE2IDUuOTk2LTI4Ljc3NyAxNy40OS4wMTYgNy4wMiA1NS44MDktMTMuNTU2LjAxNi00LjE5Ni0zNi4wOTljLTIuMjI5IDExLjg3NS0zLjkxOCAyNC4xNjktNS44NTMgMzYuMDk5bC0xNC4wODcuMDQ3LTUuOTgxLTM1Ljk1NWMtMS42OSAxMS44NS0yLjggMjQuMDI2LTQuMjEyIDM1Ljk1NWwtMTMuNzcuMDI0IDcuNjQ3LTU1Ljk1MiAxNy41MTMuMDR6IiBmaWxsPSIjMWU1OWFlIi8+PHBhdGggZD0ibTEwMS4wMTQgMzE0LjIxNiA1Ljk5Ni0yOC43NzcgMTcuNDkuMDE2IDcuMDIgNTUuODA5LTEzLjU1Ni4wMTYtNC4xOTYtMzYuMDk5Yy0yLjIyOSAxMS44NzUtMy45MTggMjQuMTY5LTUuODUzIDM2LjA5OWwtMTQuMDg3LjA0Ny01Ljk4MS0zNS45NTVjLTEuNjkgMTEuODUtMi44IDI0LjAyNi00LjIxMiAzNS45NTVsLTEzLjc3LjAyNCA3LjY0Ny01NS45NTIgMTcuNTEzLjA0eiIgZmlsbD0ibm9uZSIvPjxwYXRoIGQ9Im0xNzkuOTM2IDM0MS4zMjctMTQuMjg2LS4wOC0xLjY0Mi05LjY2OC0xMy4wNDgtLjA4LTEuOTIgOS43NzMtMTMuNzg1LjA2MyAxMS42MDQtNTUuODg4aDIwLjkyNXoiIGZpbGw9IiMxZTU5YWUiLz48cGF0aCBkPSJtMTc5LjkzNiAzNDEuMzI3LTE0LjI4Ni0uMDgtMS42NDItOS42NjgtMTMuMDQ4LS4wOC0xLjkyIDkuNzczLTEzLjc4NS4wNjMgMTEuNjA0LTU1Ljg4OGgyMC45MjV6IiBmaWxsPSJub25lIi8+PHBhdGggZD0ibTIxNi40MzEgMjg3LjEyYzguMDc1IDQuMDQ2IDcuNzY1IDE0LjEwMyA3LjI4MiAyMS42My0uODY1IDQuMDk0LTIuNDQzIDkuMDktNy4wNjggMTAuNTQybC4wMTYgMS40OTIgNy44MTMgMjAuNDk2LTEzLjc4Ni4wNTVzLTYuNzEtMTkuNzk4LTYuNzQyLTE5Ljk0Yy0uOTc1LS41MTYtMi42MTctLjUwOC0zLjU5My4wMjN2MTkuOTFsLTEzLjM3My0uMDguMDQ3LTU1Ljc3N3MyMS4xMzEtMS43ODUgMjkuNDA0IDEuNjUiIGZpbGw9IiMxZTU5YWUiLz48cGF0aCBkPSJtMjE2LjQzMSAyODcuMTJjOC4wNzUgNC4wNDYgNy43NjUgMTQuMTAzIDcuMjgyIDIxLjYzLS44NjUgNC4wOTQtMi40NDMgOS4wOS03LjA2OCAxMC41NDJsLjAxNiAxLjQ5MiA3LjgxMyAyMC40OTYtMTMuNzg2LjA1NXMtNi43MS0xOS43OTgtNi43NDItMTkuOTRjLS45NzUtLjUxNi0yLjYxNy0uNTA4LTMuNTkzLjAyM3YxOS45MWwtMTMuMzczLS4wOC4wNDctNTUuNzc3czIxLjEzMS0xLjc4NSAyOS40MDQgMS42NXoiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMzk4LjU1NSAyOTAuMThjNi4xNjMgOC42NjIgNS4wNjggMjEuMDM2IDQuNjggMzEuNzYtLjQ1MiA3LjY3OC0zLjIyIDE2LjQxMS0xMS40NzggMTguODU0LTguNjE0IDIuMjEzLTE3LjU2OSAyLjQyLTI0LjgxOS0yLjg4Ny04LjI1Ny04LjIxLTUuODE0LTIxLjcxLTYuMTIzLTMzLjAyLjU0Ny02LjY5NSAxLjk5OS0xMy43MTUgOC4yMjUtMTcuNTYyIDguNDY0LTQuNTYgMjEuODYtNC40NjUgMjkuNTE1IDIuODU2IiBmaWxsPSIjMWU1OWFlIi8+PHBhdGggZD0ibTM5OC41NTUgMjkwLjE4YzYuMTYzIDguNjYyIDUuMDY4IDIxLjAzNiA0LjY4IDMxLjc2LS40NTIgNy42NzgtMy4yMiAxNi40MTEtMTEuNDc4IDE4Ljg1NC04LjYxNCAyLjIxMy0xNy41NjkgMi40Mi0yNC44MTktMi44ODctOC4yNTctOC4yMS01LjgxNC0yMS43MS02LjEyMy0zMy4wMi41NDctNi42OTUgMS45OTktMTMuNzE1IDguMjI1LTE3LjU2MiA4LjQ2NC00LjU2IDIxLjg2LTQuNDY1IDI5LjUxNSAyLjg1NnoiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMzA3Ljg3NyAyOTcuMzIyaC0xMi4wNDdsLS4wNDggNDMuOTUtMTMuMzU3LS4wMjMtLjAwOC00NC4wMDdoLTEyLjAyN2wuMDE2LTExLjkzNyAzNy40Ny4wMDh6IiBmaWxsPSIjMWU1OWFlIi8+PHBhdGggZD0ibTMwNy44NzcgMjk3LjMyMmgtMTIuMDQ3bC0uMDQ4IDQzLjk1LTEzLjM1Ny0uMDIzLS4wMDgtNDQuMDA3aC0xMi4wMjdsLjAxNi0xMS45MzcgMzcuNDcuMDA4eiIgZmlsbD0ibm9uZSIvPjxwYXRoIGQ9Im0zMjYuNTgyIDMwNy42NCAxMS45OTMuMDg3LjA1NS0yMi4zNjggMTMuNjgzLS4wNHY1NS45NTJsLTEzLjY2Ny4wNjN2LTIxLjc3M2wtMTIuMDQ5LjAwOC0uMDc5IDIxLjY3LTEzLjczOC4wMjQuMDQtNTUuOTQ0IDEzLjY4Mi0uMDI0eiIgZmlsbD0iIzFlNTlhZSIvPjxwYXRoIGQ9Im0zMjYuNTgyIDMwNy42NCAxMS45OTMuMDg3LjA1NS0yMi4zNjggMTMuNjgzLS4wNHY1NS45NTJsLTEzLjY2Ny4wNjN2LTIxLjc3M2wtMTIuMDQ5LjAwOC0uMDc5IDIxLjY3LTEzLjczOC4wMjQuMDQtNTUuOTQ0IDEzLjY4Mi0uMDI0eiIgZmlsbD0ibm9uZSIvPjxwYXRoIGQ9Im00MzkuODg4IDMyMS4xNzIuMDE2LTM1Ljg2aDEyLjQ4NXY1Ni4wNTVoLTE4LjM1NWwtOS43NDgtMzMuNjR2MzMuNjRoLTEyLjAxN3YtNTYuMDU1aDE4LjMyM3oiIGZpbGw9IiMxZTU5YWUiLz48cGF0aCBkPSJtNDM5Ljg4OCAzMjEuMTcyLjAxNi0zNS44NmgxMi40ODV2NTYuMDU1aC0xOC4zNTVsLTkuNzQ4LTMzLjY0djMzLjY0aC0xMi4wMTd2LTU2LjA1NWgxOC4zMjN6IiBmaWxsPSJub25lIi8+PHBhdGggZD0ibTE2MS43NjQgMzIwLjk0LTguNzczLS4wMzEgNC41MDUtMjMuODQzYzEuODY0IDcuNTgyIDIuODcyIDE1LjkxMSA0LjI2OCAyMy44NzUiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJtMTYxLjc2NCAzMjAuOTQtOC43NzMtLjAzMSA0LjUwNS0yMy44NDNjMS44NjQgNy41ODIgMi44NzIgMTUuOTExIDQuMjY4IDIzLjg3NXoiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMjA4LjIzNiAyOTcuOTExYzIuMzI0IDIuNTc4IDIuNDkgNi45IDEuMzMyIDEwLjAzNC0uODA5IDEuMTI2LTEuMjg1IDIuNDAzLTMuMzMxIDIuNzEzbC01LjU5Mi4wNTUtLjAxNi0xMy43NDZzNS41OTItLjU0NyA3LjYwNy45NDQiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJtMjA4LjIzNiAyOTcuOTExYzIuMzI0IDIuNTc4IDIuNDkgNi45IDEuMzMyIDEwLjAzNC0uODA5IDEuMTI2LTEuMjg1IDIuNDAzLTMuMzMxIDIuNzEzbC01LjU5Mi4wNTUtLjAxNi0xMy43NDZzNS41OTItLjU0NyA3LjYwNy45NDR6IiBmaWxsPSJub25lIi8+PHBhdGggZD0ibTM4Ny4yMTMgMjk3LjYyNGMzLjgxNSA2LjY5NCAyLjA2MiAxOC4yMjcgMS43NjkgMjcuMTAzLS40NTIgMi4xNTgtLjg4IDQuNjI1LTIuOTU5IDUuNzUtMi41MzggMS4xMzUtNi4zODUgMS4xNTktOC42My0uNjgxLTIuMDk0LTIuNzc2LTEuODA4LTMuNDI3LTIuMzcxLTYuODYxLTEuMTc0LTcuMTk1LTIuMTY2LTE4LjI1MiAxLjYyNi0yNC44NTEgMi40OTgtMi42MzMgNy44Ni0yLjg5NSAxMC41NjUtLjQ2IiBmaWxsPSIjZmZmIi8+PHBhdGggZD0ibTM4Ny4yMTMgMjk3LjYyNGMzLjgxNSA2LjY5NCAyLjA2MiAxOC4yMjcgMS43NjkgMjcuMTAzLS40NTIgMi4xNTgtLjg4IDQuNjI1LTIuOTU5IDUuNzUtMi41MzggMS4xMzUtNi4zODUgMS4xNTktOC42My0uNjgxLTIuMDk0LTIuNzc2LTEuODA4LTMuNDI3LTIuMzcxLTYuODYxLTEuMTc0LTcuMTk1LTIuMTY2LTE4LjI1MiAxLjYyNi0yNC44NTEgMi40OTgtMi42MzMgNy44Ni0yLjg5NSAxMC41NjUtLjQ2eiIgZmlsbD0ibm9uZSIvPjxwYXRoIGQ9Im0yNzIuNjUyIDM0MS4zMjctMTQuMjg2LS4wOC0xLjY0Mi05LjY2OC0xMy4wMDgtLjA4LTEuOTQzIDkuNzczLTEzLjc4Ni4wNjMgMTEuNTg5LTU1Ljg4OGgyMC45MzJ6IiBmaWxsPSIjMWU1OWFlIi8+PHBhdGggZD0ibTI3Mi42NTIgMzQxLjMyNy0xNC4yODYtLjA4LTEuNjQyLTkuNjY4LTEzLjAwOC0uMDgtMS45NDMgOS43NzMtMTMuNzg2LjA2MyAxMS41ODktNTUuODg4aDIwLjkzMnoiIGZpbGw9Im5vbmUiLz48cGF0aCBkPSJtMjU0LjUxMSAzMjAuOTQtOC43OTYtLjAzMSA0LjUyMS0yMy44NDNjMS44NCA3LjU4MiAyLjg4IDE1LjkxMSA0LjI3NSAyMy44NzUiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJtMjU0LjUxMSAzMjAuOTQtOC43OTYtLjAzMSA0LjUyMS0yMy44NDNjMS44NCA3LjU4MiAyLjg4IDE1LjkxMSA0LjI3NSAyMy44NzV6IiBmaWxsPSJub25lIi8+PHBhdGggZD0ibTUxOS44NSAzODcuNDdjMi4yMiAwIDQuMjA0LS4xNjYgNC4yMDQtMi44MjMgMC0yLjEzNC0xLjk0NC0yLjUzOS0zLjc2LTIuNTM5aC0zLjU3djUuMzYyem0tMy4xMjUgOS43MTdoLTIuNjI2di0xNy4yOTJoNi41OTFjNC4wNzcgMCA2LjEgMS41IDYuMSA0LjkxOCAwIDMuMDk0LTEuOTQzIDQuNDQyLTQuNDczIDQuNzZsNC45MTcgNy42MTRoLTIuOTM0bC00LjU3LTcuNTA0aC0zLjAwNXptMy4xNjQgMy44NDdjNi43ODIgMCAxMi4xMzYtNS4zMTQgMTIuMTM2LTEyLjUzMyAwLTcuMTA3LTUuMzU0LTEyLjQ1My0xMi4xMzYtMTIuNDUzLTYuODUzIDAtMTIuMjE1IDUuMzQ2LTEyLjIxNSAxMi40NTMgMCA3LjIxOSA1LjM2MiAxMi41MzMgMTIuMjE1IDEyLjUzM20tMTUuMjI5LTEyLjUzNGMwLTguNjA2IDYuOTgtMTQuOTUxIDE1LjIzLTE0Ljk1MSA4LjE3IDAgMTUuMTUgNi4zNDUgMTUuMTUgMTQuOTUxIDAgOC42ODYtNi45OCAxNS4wMjQtMTUuMTUgMTUuMDI0LTguMjUgMC0xNS4yMy02LjMzOC0xNS4yMy0xNS4wMjQiIGZpbGw9IiMxZTU5YWUiLz48L3N2Zz4=",
  "Valero Energy": "data:image/svg+xml;base64,PHN2ZyBoZWlnaHQ9IjE3NzgiIHZpZXdCb3g9Ii4xMzIgLjEzMiAzMS44MDUxMjI4IDIyLjYzNiIgd2lkdGg9IjI1MDAiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyI+PHBhdGggZD0ibTcuMTE1LjEzMmg1LjUyNmwxLjI3MiAzLjQ0My4wMDEuMDAzLjEwMi4wNC4zMjUuODY4aC4wMDNjMS4xNDcuMDI2IDEuNDQ0LjM1NCAxLjUyLjU0OC4wNTguMTQ4LjAzLjMxOS0uMDguNTExLS4xNy0uMTc2LS41NTMtLjMyNi0xLjI3My0uMzU0bC40OCAxLjMwM2MtLjU2OC41OS0xLjI5NyAxLjQ3MS0uOTMyIDIuMTg2LjI2LjUxLjk4Ljc3IDIuMTQzLjc3IDMuNzQ0IDAgMTAuNTItMi42MDIgMTEuMzUyLTIuOTcyYS40NTMuNDUzIDAgMCAwIC4yNzMtLjM4Ny41MjIuNTIyIDAgMCAxIC40MDYuNTM2LjUyOS41MjkgMCAwIDEgLS4zMi40NThjLS44MjguMzY4LTQuOTkgMS45MzQtOC40MjMgMi42NjNsLTEuNDUzIDMuNjIzaC00LjI2NWMtLjg3MiAwLTEuMy0uMDUzLTEuODkyLTEuMzg1LS4zMS0uNjk3LTEuMzQ2LTMuMzQxLTIuNDAzLTUuOTY3LTEuNjE4LjUwMy0zLjczNyAxLjI0Ni00Ljk5NiAxLjkwNmEuNTA0LjUwNCAwIDAgMSAtLjcyNi0uNjAyLjQyNy40MjcgMCAwIDAgLjIzOS4wNzZoLjAwNmMuMDc0IDAgLjE0Ny0uMDIuMjEtLjA1NSAxLjQ0OC0uNzYgMy45OTMtMS41OTIgNC45ODMtMS45MDNsLS4zMTQtLjc3Mi4wMy0uMDZ6bTAgMCAxLjc5NCA0LjQ3OG03LjgwMS4xMTVjLjIyNS42MDUuMDExIDEuMjA1LS42NDggMS44MzYtLjEzNy4xMjctMS4zMzQgMS4yNDYtMS4xNzQgMS43MjguMDc1LjIyMi40MTUuMzMgMS4wNDIuMzMuOTM2IDAgMi40NzgtLjI0MyA0LjI4My0uNjc3bDMuMTMtNy44MWgtNS41MjVsLTEuNTE2IDQuMDk5Yy4xOTkuMTQuMzM2LjI5OS40MDguNDk0bTEzLjYxMiAxNS4zNjNjMCAuNzg4LS4yNSAxLjQxLS43NSAxLjg2MS0uNDk3LjQ1NS0xLjIwMi42ODMtMi4xMTUuNjgzLS45MDUgMC0xLjYxLS4yMjgtMi4xMS0uNjgzLS41MDEtLjQ1Mi0uNzUzLTEuMDczLS43NTMtMS44NjEgMC0uNzk1LjI1Mi0xLjQyLjc1Mi0xLjg3LjUwMi0uNDUxIDEuMjA2LS42NzcgMi4xMTEtLjY3Ny45MDkgMCAxLjYxNC4yMjcgMi4xMTQuNjgyLjUuNDUyLjc1MSAxLjA3NC43NTEgMS44NjVtLTEuNjguMDA4YzAtLjI3LS4wMzEtLjUxOC0uMDktLjcwNmExLjE4NyAxLjE4NyAwIDAgMCAtLjI0NC0uNDUyLjg5NS44OTUgMCAwIDAgLS4zNzQtLjI0NyAxLjQ5MiAxLjQ5MiAwIDAgMCAtLjQ3NS0uMDdjLS4xNyAwLS4zMjEuMDItLjQ1Ni4wNmEuOTIzLjkyMyAwIDAgMCAtLjM3Ny4yMzYgMS4xOCAxLjE4IDAgMCAwIC0uMjU2LjQ1NGMtLjA2My4xOTMtLjA5Ni40NDUtLjA5Ni43MjVzLjAzLjUyMi4wOTIuN2MuMDYuMTc5LjE0LjMyLjIzNi40MjcuMDk5LjEwOS4yMjQuMTg5LjM3My4yMzguMTUuMDUzLjMxNy4wNzYuNDk5LjA3Ni4xNSAwIC4zMDItLjAyMy40NTctLjA3NmEuODM4LjgzOCAwIDAgMCAuMzczLS4yMjZjLjExLS4xMjEuMTk0LS4yNjYuMjUyLS40MzUuMDU1LS4xNy4wODUtLjQxNC4wODUtLjcwNG0tMTcuMjY1LS44ODJ2My4yOTloLTEuNzFsLjAwMi0uMjI0Yy0uODIyLjQ3OS0yLjAzNi4yNy0yLjE4NC4yNDdhMS40NTUgMS40NTUgMCAwIDEgLS40MjMtMi43NjNjLjA1Ny0uMDI2LjU3Mi0uMzE3IDEuNzUyLS4zMTdoLjkyOGMwLS4yNjMtLjA5Ni0uNTQ4LS4zMDQtLjY4LS41MjgtLjMzNC0yLjU0NS0uMDM1LTIuNTQ1LS4wMzVsLjM4OC0xLjA1M2E3LjYgNy42IDAgMCAxIDEuMzU1LS4xNDJjLjk1NSAwIDEuNjUuMTM3IDIuMDg2LjQxMi40MzcuMjc1LjY1NS42OTMuNjU1IDEuMjU2bS0xLjY1IDEuMTZjLS45NzUgMC0xLjM3NC4wNjktMS4zNzQuMDY5YS43MTcuNzE3IDAgMCAwIC0uMzgxLjIwOC41MTQuNTE0IDAgMCAwIC4yOTIuODYzYy4wNzQuMDEzIDEuNDYzLjIxMiAxLjQ2My0uNTU3em0tNC40MzQtNC4xMzctMS42ODYgNC40OTQtMS42Ny00LjQ5NGgtMS44MDRsMi4xNTMgNS4zNjljLjIwOC41My43MjMuOTA1IDEuMzI3LjkwNWguOTczbDIuNDk3LTYuMjc0em02LjkxMy45NnY1LjMxNmguNjk2Yy41MyAwIC45Ni0uNDMuOTYtLjk2di01LjMxNmgtLjY5N2MtLjUzIDAtLjk1OS40My0uOTU5Ljk2bTcuODY4IDIuNjRzLjAwMi4zOSAwIC41MzdoLTMuODY5Yy4wMTYuMjIuMDgzIDEuMTcgMS43NzUgMS4xNy4yMDMgMCAuNjk4LjA1IDEuOTMyLS4xNjV2MS4wODdjLTEuMDI1LjE4NS0xLjgyNy4xNTgtMi4xMTIuMTU4LTIuOTU2IDAtMy4yNDQtMS43MDctMy4yNDQtMi41MDYgMC0uODA4LjM0OS0yLjU3MiAyLjk2LTIuNTcyLjg1IDAgMS40ODguMTk2IDEuOTE3LjU5My40MTcuMzg0LjY0Ljk3LjY0IDEuNjk4bS0xLjMzOC0uMzhjLS4wMTYtLjMyNi0uMS0uODM3LTEuMjI3LS44MzctMS4xNTUgMC0xLjI1Mi41OTQtMS4yNzUuODM2em00LjAzNS0xLjkwMmMtLjc5LjAzMy0xLjg4My40NC0xLjg4MyAxLjU4MnYzLjM3NmgxLjY1di0yLjg1N2MwLS43NDQuNTQ4LTEuMDUgMS44MDQtLjc0NHYtMS4yMjJzLS40OTMtLjE0OC0xLjIxNC0uMTQ4Yy0uMTE0IDAtLjIzMy4wMDQtLjM1Ny4wMTNtOS4xMTMuNjI4YzAgLjE2Ny0uMDU5LjMxMS0uMTc3LjQzYS41ODguNTg4IDAgMCAxIC0uNDMuMTc4LjU4OC41ODggMCAwIDEgLS40My0uMTc4LjU4OC41ODggMCAwIDEgLS4xNzgtLjQzYzAtLjE2Ny4wNi0uMzEyLjE3OC0uNDNhLjU5LjU5IDAgMCAxIC40My0uMTguNTkuNTkgMCAwIDEgLjQzLjE4LjU4OC41ODggMCAwIDEgLjE3Ny40M20tLjI4Mi4zMjdhLjQ1Mi40NTIgMCAwIDAgLjEzNS0uMzI3LjQ0OC40NDggMCAwIDAgLS4xMzUtLjMyNy40NC40NCAwIDAgMCAtLjMyNS0uMTM2LjQ0LjQ0IDAgMCAwIC0uMzI2LjEzNmMtLjA5LjA5LS4xMzMuMi0uMTMzLjMyN2EuNDUuNDUgMCAwIDAgLjEzMy4zMjdjLjA5LjA5LjE5OS4xMzYuMzI2LjEzNmEuNDQ2LjQ0NiAwIDAgMCAuMzI1LS4xMzZtLjAxLS4wNDVoLS4yMDNsLS4xNjctLjIxaC0uMDM3di4yMWgtLjE1OHYtLjU5MmguMjE5Yy4wNCAwIC4wNzIgMCAuMDk1LjAwNC4wMjUuMDA0LjA1LjAxMi4wNzMuMDI2LjAyOC4wMTUuMDQ4LjAzNS4wNi4wNTdzLjAyLjA1LjAyLjA4MmEuMTY1LjE2NSAwIDAgMSAtLjAzNy4xMTIuMjI5LjIyOSAwIDAgMSAtLjA3OS4wNnptLS40MDctLjMzaC4wMjJjLjAyMSAwIC4wNC0uMDAxLjA1Ny0uMDA0YS4wODMuMDgzIDAgMCAwIC4wMzctLjAxNi4wNjMuMDYzIDAgMCAwIC4wMTgtLjAyMy4xMDYuMTA2IDAgMCAwIC4wMDctLjAzOS4wNjYuMDY2IDAgMCAwIC0uMDA3LS4wMjguMDQuMDQgMCAwIDAgLS4wMi0uMDJjLS4wMS0uMDA3LS4wMi0uMDEtLjAzMy0uMDFzLS4wMjctLjAwNC0uMDQ4LS4wMDRoLS4wMzN6bTAgMCIgZmlsbD0iIzAwNmVhYiIvPjxwYXRoIGQ9Im05LjI2NiA1LjQ5OGMtMS42Mi41MDMtMy43NTQgMS4yNDktNS4wMTggMS45MTJhLjUwMy41MDMgMCAwIDEgLS40Ni0uODk2YzEuNDU4LS42OCAzLjUxOC0xLjQwNiA1LjEyMS0xLjkwM3ptMTguMTM4LjA0M2EuNTIzLjUyMyAwIDAgMCAtLjI3LjA2Yy00Ljg4MyAyLjA5NS0xMS44NTIgMy41OTUtMTIuMTcxIDIuNjY0LS4xNTUtLjQ0NyAxLjE1Mi0xLjY0NiAxLjE1Mi0xLjY0Ni42MTctLjU5Mi45MjQtMS4yMjcuNjY4LTEuOTIxLS4yODItLjc2NS0xLjY0MS0xLjEzNC0yLjg2OS0xLjEyMi4wNjMuMTc0LjE5Ni41MzIuMzY0Ljk4NWwuMDYzLjAwMWMuOTczLjAyMiAxLjM1OS4yNjMgMS40NTEuNS4xMDguMjc3LS4xNy42MDUtLjMwMy43NS0uMDk2LjEwNS0uNTc2LjY1LS41NzYuNjUtLjQ4Ni41MDQtMS4zMzQgMS40NDktLjkyMyAyLjI1NCAxLjI3NiAyLjUwMiAxMi4xNDQtMS41MjIgMTMuNTk2LTIuMTY4YS41MjUuNTI1IDAgMCAwIC0uMTgyLTEuMDA3IiBmaWxsPSIjZmZjZjAwIi8+PC9zdmc+",
  "Sunoco": "data:image/svg+xml;base64,PHN2ZyBoZWlnaHQ9IjE1ODIiIHZpZXdCb3g9IjAgMCA5MC4yODA5OTk5OTk5OTk5OSA1NS44NzUiIHdpZHRoPSIyNTAwIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciPjxwYXRoIGQ9Ik0xNC41MzEgMGwtLjU5NCA2LjcxOS02LjI1IDIuNSAxMS40MzggOC41IDEuNDA2LS40MDcgMi4zNzUgMS43ODItMS43ODEuNzgxaC03LjVjLTEuMzY5IDAtMy4xNzIuNzctMy45MDYgMi40NjkgMCAwLS45NDkgMi4yMi0xLjMxMyAzLjA2MkwwIDI5LjAzMWw1LjcxOSAyLjU5NGMtLjI1Ni41OTYtLjUgMS4xMjMtLjUgMS4xMjUtLjY0IDEuNTA0LS41NjMgMy4wMDUuMjE4IDQuMTg4Ljc0NSAxLjEyNSAyLjA0NyAxLjc4IDMuNDcgMS43OGgxMy4xODdsMjIuNTMxIDkuODEzIDExLjQwNi00Ljg0M0w2NC41OTQgNTBsLTEuOTA2IDIuNTYzIDE3LjU2MiAzLjMxMi04LjI4MS0xNS44NDQtMiAyLjcxOS00LjMxMy0zLjE4OCAxLjk2OS0uODQzaDguNzgxYzEuMzkgMCAzLjE0OS0uODMzIDMuODc1LTIuNDM4bDEuNjU2LTMuNjU2IDguMzQ0LTMuNTk0LTUuNjg3LTIuMzc1LjU5NC0xLjMxMmMuNTYtMS4yNDIuNDkyLTIuNTcyLS4xODgtMy42MjUtLjc0OC0xLjE1OC0yLjEyLTEuODQ0LTMuNjg4LTEuODQ0SDY4LjcyTDQ0LjY1NiA5Ljc4MSAzMi41IDE1bC02LjU2My00Ljg3NS4wOTQtMS42MjV6bTU0Ljc4MiAzOS4yMTljLS41NzYgMC0xLjA2My40MzItMS4wNjMgMS4wMzFhMS4wNjMgMS4wNjMgMCAwIDAgMi4xMjUgMGMwLS41OTktLjQ5NS0xLjAzMS0xLjA2My0xLjAzMXptMCAuMTg3Yy40NyAwIC44NDMuMzUuODQzLjg0NCAwIC41MDItLjM3Mi44NzUtLjg0NC44NzUtLjQ3NyAwLS44NDMtLjM3Mi0uODQzLS44NzVhLjgyLjgyIDAgMCAxIC44NDQtLjg0NHptLS40MDcuMjV2MS4yMTloLjE4OHYtLjUzMWguMjE5bC4zMTIuNTMxaC4yMTlsLS4zNDQtLjUzMWMuMTc4LS4wMjMuMzEzLS4xMjkuMzEzLS4zNDQgMC0uMjM3LS4xNTQtLjM0NC0uNDM4LS4zNDR6bS4xODguMTU3aC4yNWMuMTI2IDAgLjI4MS4wMzguMjgxLjE4NyAwIC4xODUtLjE1OC4xODgtLjMxMy4xODhoLS4yMTh6IiBmaWxsPSIjMGE0YjhmIi8+PHBhdGggZD0iTTE1Ljc1IDIuNzE5bC0uNDY5IDUtNC42NTYgMS44NzUgOC44MTMgNi41MzEgMS4zNzUtLjQwNiAzLjYyNSAyLjcxOSA2LjUtMi43ODItNi40Ny00Ljg0NC4wNjMtMS41OTN6bTQ4LjM0NCAzNy41TDU3LjU5NCA0M2w5LjAzMSA2LjcxOS0xLjM3NSAxLjg0MyAxMi4zMTMgMi4zNDQtNS44MTMtMTEuMTI1LTEuNSAyLjAzMnoiIGZpbGw9IiNmMDRhNGUiLz48cGF0aCBkPSJNNDQuNjg4IDExLjU2M2wtMjMuMjIgOS45NjhoLTcuODQzYy0uODQ4IDAtMS45NTkuNTA3LTIuMzc1IDEuNDY5bC0xLjU5NCAzLjY1Ni01LjU2MiAyLjQwNyAzLjc4MSAxLjcxOC0xLjEyNSAyLjYyNWMtLjkyNiAyLjE3OS40OTUgMy42NTcgMi4xNTYgMy42NTdoMzIuOTY5bC0uMDk0LjI1LTE1LjgxMiAxLjMxMiAxOC42ODcgOC4xMjUgMjIuNjI1LTkuNjg4aDkuMTI1Yy44NDggMCAxLjk1My0uNTMzIDIuMzc1LTEuNDY4bDEuOTM4LTQuMjUgNS4zMTItMi4yODItMy42MjUtMS41M3MuMzc5LS44NzcgMS4yODEtMi44NzZjLjc4NC0xLjczNi0uNTMyLTMuMTI1LTIuMzc0LTMuMTI1aC0zMy4yNWwuMDkzLS4yNSAxNi42MjUtMS4yNXpNMTUuMjggMjMuMTg3aDYuMDYzYy45NTIgMCAxLjQxMS42NCAxLjAzMSAxLjYyNWwtLjk2OSAyLjM0NGgtMy44NDNsLjUzLTEuMjgxaC0yLjA2MmwtLjgxMiAxLjk2OSA0IDEuMjgxYy42Ny4yMjMuOTUzLjg5LjY1NiAxLjU5NGwtMS41MzEgMy42NTZjLS4yNTcuNjExLTEuMjQxIDEuMTU2LTIuMTU3IDEuMTU2aC02LjI1Yy0uNzYzIDAtMS41MDgtLjQ4Ni0xLjA2Mi0xLjY1NmwuOTY5LTIuMzQ0aDMuODQ0bC0uNTk0IDEuNDA3aDIuMDMxbC43MTktMS44MTMtNC0xLjI4MWMtLjY3OS0uMjE4LS45MDMtLjkxNS0uNjI1LTEuNjI1bDEuNTMxLTMuNjg4Yy40MDMtLjg4MyAxLjE5OC0xLjM0MyAyLjUzMS0xLjM0M3ptOS42MjUgMGgzLjg0NGwtNC4wNjMgOS43NWgyLjAzMmw0LjA2Mi05Ljc1aDMuODQ0cy00LjQ3MyAxMC42MzQtNC42NTYgMTEuMTI1Yy0uMjI5LjYxMy0xLjIyMiAxLjIyLTIuMTg4IDEuMjJIMjEuNWMtMS4wNTQgMC0xLjM5My0uNzk2LTEuMDMxLTEuNjU3LjI5OS0uNzEgNC40MzctMTAuNjg4IDQuNDM3LTEwLjY4OHptMTEuNTYzIDBoMy44NzVsLjk2OCA1Ljg0NCAyLjE4OC01LjI1LTIuNTMxLS41OTNINDcuNUw0Mi4zNzUgMzUuNTNoLTMuNjg4bC0xLjA2Mi01Ljc1LTIuNDA2IDUuNzVoLTMuODc1em0xNC44NzUgMGg2YzEuMDEgMCAxLjQ0NS43MyAxLjA2MiAxLjYyNWwtMy45NjggOS41Yy0uMy43MjItMS4yNTcgMS4yMi0yLjA5NCAxLjIySDQ2Yy0xLjAxNiAwLTEuNDM3LS43NTctMS4wNjMtMS42NTdsMy44NzYtOS4zNDRjLjQ0LTEuMDU2IDEuNTQyLTEuMzQzIDIuNTMtMS4zNDN6bTExLjU2MiAwaDZjMS4wMSAwIDEuNDQ1LjczIDEuMDYzIDEuNjI1TDY5IDI3LjE1N2gtMy44MTNsLjUtMS4yODFoLTIuMDNsLTIuOTM4IDcuMDYzaDIuMDMxbC43ODEtMS44NDRoMy44MTNMNjYgMzQuMzEyYy0uMjk5LjcyMi0xLjI1NiAxLjIyLTIuMDk0IDEuMjJoLTYuMzQzYy0xLjAxNyAwLTEuNDM4LS43NTctMS4wNjMtMS42NTdsMy44NzUtOS4zNDRjLjQ0MS0xLjA1NiAxLjU0Mi0xLjM0MyAyLjUzMS0xLjM0M3ptMTEuNTYzIDBoNmMxLjAxMSAwIDEuNDQ1LjczIDEuMDYyIDEuNjI1bC0zLjkzNyA5LjVjLS4zLjcyMi0xLjI4OCAxLjIyLTIuMTI1IDEuMjJoLTYuMzQ0Yy0xLjAxNiAwLTEuNDM3LS43NTctMS4wNjMtMS42NTdsMy45MDctOS4zNDRjLjQ0MS0xLjA1NiAxLjUxMS0xLjM0MyAyLjUtMS4zNDN6bS0yMi4zNzUgMi42ODhsLTIuOTM4IDcuMDYzaDIuMDMybDIuOTM3LTcuMDYzem0yMy4xMjUgMGwtMi45MzggNy4wNjNoMi4wNjNsMi45MzctNy4wNjN6IiBmaWxsPSIjZmZlMjM0Ii8+PC9zdmc+",
  "Gulf": "data:image/svg+xml;base64,PHN2ZyBlbmFibGUtYmFja2dyb3VuZD0ibmV3IDAgMCAyNDkyLjkgMjI2NC43IiB2aWV3Qm94PSIwIDAgMjQ5Mi45IDIyNjQuNyIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIj48cGF0aCBkPSJtMjQ4Mi40IDEzMDguMmMxMy41LTk1LjkgMTQuMS0yNDAuMSAxLjUtMzUwLjUtMTYuOS0xNzIuMS0xMjYtMjE5LjktMTcxLjUtMjMyLjQtODEuNS0yMDkuNy0yMjIuNy0zODkuMS00MDguOC01MTkuMi0xOTMuMS0xMzQuOC00MjAuMy0yMDYuMS02NTcuMS0yMDYuMXMtNDY0LjEgNzEuMy02NTcgMjA2LjFjLTE4Ni4zIDEzMC4xLTMyNy40IDMwOS41LTQwOC45IDUxOS4yLTQ1LjYgMTIuNS0xNTQuNiA2MC4zLTE3MS41IDIzMi42LTEyLjYgMTEwLjItMTIgMjU0LjMgMS41IDM1MC4zIDEzLjMgMTQwLjcgOTcuNSAyMTAuOCAxNjkuNSAyMjkuOSA4MS4zIDIxMCAyMjIuNCAzODkuNyA0MDguNyA1MjAuMSAxOTMuMSAxMzUuMSA0MjAuNSAyMDYuNSA2NTcuNiAyMDYuNXM0NjQuNS03MS40IDY1Ny42LTIwNi41YzE4Ni4zLTEzMC40IDMyNy41LTMxMC4xIDQwOC43LTUyMC4xIDcyLjItMTkuMSAxNTYuNC04OS4yIDE2OS43LTIyOS45eiIgZmlsbD0iIzFmMzA3NSIvPjxwYXRoIGQ9Im0yMjk2LjUgMTUwNi41Yy01LjggMS4yLTEwLjYgNS4zLTEyLjYgMTAuOC03OC4zIDIwNy4yLTIxNi40IDM4NC40LTM5OS42IDUxMi42LTE4Ny4zIDEzMS00MDcuOCAyMDAuMy02MzcuOCAyMDAuM3MtNDUwLjYtNjkuMy02MzcuOS0yMDAuM2MtMTgzLjEtMTI4LjEtMzIxLjMtMzA1LjQtMzk5LjYtNTEyLjYtMi4xLTUuNS02LjktOS42LTEyLjYtMTAuOC02Mi41LTEyLjktMTM5LjYtNzMuNi0xNTEuNi0yMDIuMSAwLS4zLS4xLS41LS4xLS44LTEzLjItOTMuNC0xMy43LTIzNC0xLjQtMzQyIDE1LjUtMTU4IDExMi43LTE5NS45IDE1My44LTIwNC45IDUuNy0xLjIgMTAuNC01LjMgMTIuNC0xMC43IDc4LjUtMjA2LjkgMjE2LjctMzgzLjggMzk5LjctNTExLjYgMTg3LjEtMTMwLjggNDA3LjUtMTk5LjkgNjM3LjMtMTk5LjlzNDUwLjEgNjkuMSA2MzcuMyAxOTkuOWMxODMgMTI3LjkgMzIxLjIgMzA0LjggMzk5LjcgNTExLjYgMi4xIDUuNCA2LjcgOS41IDEyLjQgMTAuNyA0MS4xIDkgMTM4LjIgNDYuOSAxNTMuNyAyMDQuNiAxMi40IDEwOC4zIDExLjggMjQ4LjktMS40IDM0Mi4zIDAgLjMtLjEuNS0uMS44LTExLjkgMTI4LjUtODkuMSAxODkuMi0xNTEuNiAyMDIuMXoiIGZpbGw9IiNmZmYiLz48cGF0aCBkPSJtMjI1Ny42IDc1MGMtMTU1LjUtNDAyLjktNTQ5LjYtNjg5LTEwMTEuMS02ODlzLTg1NS43IDI4Ni4yLTEwMTEuMiA2ODljNjM3LjUtMTA2LjYgMTM4NC44LTExMi4zIDIwMjIuMyAwem0wIDc2NC42Yy0xNTUuNSA0MDIuOS01NDkuNiA2ODktMTAxMS4xIDY4OXMtODU1LjYtMjg2LjEtMTAxMS4xLTY4OWM2MzcuNCAxMDYuNiAxMzg0LjcgMTEyLjQgMjAyMi4yIDB6IiBmaWxsPSIjZWM1ZTA0Ii8+PHBhdGggZD0ibTE2NTEuOCA4OTMuNWgxOTIuNnY1MjMuMmgtMTkyLjZ6bS0zNjEuMyAxODRoMTkyLjZ2MzM5LjJoLTE5Mi42di0xMS41Yy0zNy40IDIzLTEzNS4xIDI1LjktMTU4LjEgMjUuOXMtMTgxLjEtMjAuMS0xODEuMS0xNDAuOXYtMjEyLjdoMTkyLjZ2MTU4LjFjLTIuOSAzMS42IDguNiA4MC41IDY2LjEgODAuNXM4MC41LTE3LjIgODAuNS02Ni4xem03NTUuMSAzMzkuMnYtMjA0LjFoLTgwLjV2LTEzNS4xaDgwLjV2LTg2LjJjMi45LTU3LjUgMzEuNi0xMDYuNCAxMTcuOS0xMDYuNHMxMzIuMiAxMS41IDE4NCA0NmwtMi45IDEwMC42Yy01NC42LTMxLjYtMTEzLjUtNDAuMi0xMTMuNSAxMS41djM0LjVoODAuNXYxMzUuMWgtODAuNnYyMDQuMXptLTE1MzcuOS0yMTguNXYtMTAzLjVoMjkzLjJ2MzIxLjloLTE5Mi42di0xMS41Yy0zNy40IDExLjUtMTA3LjggMTEuMS0xNDUuMiAxMS41LTEzOCAxLjQtMzIzLjQtODQuOC0zMjMuNC0yOTcuNXMyMDIuNi0zMDcuNiAzMzcuOC0zMDcuNmMxMzUuMSAwIDIzNy4xIDM4LjggMjgzLjEgNjcuNXYxMTIuMWMtNjMuMi0yMC4xLTEyMy42LTQ4LjktMjA0LjEtNDguOXMtMjAxLjIgNDguOS0xOTguMyAxODYuOCAxMDYuNCAxNjEgMTQ5LjUgMTYxIDg2LjItMTAuMSAxMDAuNi0zMC4ydi02MS44aC0xMDAuNnptMTgyNC42IDE3Ny4zYy00LjQtNC41LTEwLjUtNy4xLTE2LjgtNy02LjEtLjEtMTIgMi4zLTE2LjQgNi41LTQuOSA0LjQtNy42IDEwLjgtNy40IDE3LjMgMCA2LjcgMi4zIDEyLjMgNi45IDE2LjlzMTAuMiA2LjkgMTYuOSA2LjljNi41IDAgMTItMi4yIDE2LjctNi43IDQuOC00LjYgNy4xLTEwLjMgNy4xLTE3LjEgMC02LjYtMi4zLTEyLjItNy0xNi44eiIgZmlsbD0iIzFmMzA3NSIvPjxwYXRoIGQ9Im0yMzI5LjQgMTM3OC41YzMuOCAzLjkgNS43IDguNSA1LjcgMTMuOCAwIDUuNC0xLjkgMTAuMS01LjcgMTQtMy42IDMuOC04LjYgNS45LTEzLjkgNS44LTUuNCAwLTEwLTEuOS0xMy45LTUuOC0zLjgtMy43LTUuOS04LjgtNS44LTE0IDAtNS4zIDEuOS05LjkgNS43LTEzLjggMy44LTQgOC41LTUuOSAxNC01LjkgNS40IDAgMTAuMSAxLjkgMTMuOSA1Ljl6IiBmaWxsPSIjZmZmIi8+PHBhdGggZD0ibTIzMTIgMTM5Ni4yaDEuNWwxLjUuMWMuOCAwIDEuNi4yIDIuNC40LjkuMyAxLjYgMSAxLjkgMS45LjIuNi4zIDEuNi40IDMuMnMuMiAyLjguNCAzLjZoNi42bC0uMi0uN2MtLjEtLjMtLjItLjUtLjItLjhzMC0uNSAwLS44di0yLjRjMC0yLjctLjgtNC43LTIuMy01LjktMS4xLS44LTIuNC0xLjMtMy43LTEuNSAxLjctLjEgMy4yLS44IDQuNi0xLjggMS4yLTEgMS45LTIuNiAxLjktNC44IDAtMi45LTEuMi01LTMuNS02LjMtMS42LS44LTMuNC0xLjMtNS4yLTEuNC0xLjggMC0zLjYtLjEtNS40IDBoLTcuM3YyNi40aDYuOXoiIGZpbGw9IiMxZjMwNzUiLz48cGF0aCBkPSJtMjMxOC41IDEzOTAuNWMtMS4xLjctMi40IDEtMy44IDFoLTIuN3YtNy42aDEuN2MxLjcgMCAzLjEuMiA0IC41IDEuNC42IDIuMSAxLjYgMi4xIDNzLS40IDIuNC0xLjMgMy4xeiIgZmlsbD0iI2ZmZiIvPjwvc3ZnPg==",
  "Citgo Petroleum": "data:image/svg+xml;base64,PHN2ZyBoZWlnaHQ9IjI1MDAiIHZpZXdCb3g9IjEuOTAzIDEuODg0IDEyNi4xOTUgMTM3LjEyMyIgd2lkdGg9IjIzMjEiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyI+PHBhdGggZD0ibTMwLjYzNSAxMjguMTY0djYuODg4Yy0xLjQxMy43OTUtOC4xNTMgMy45NTUtMTUuNzUzIDEuNDc1LTQuMzI3LTEuNDE1LTYuMzYtNS41NjUtNi44LTcuNDItLjQ0Mi0xLjg1NS0zLjExNS0xNy4yNTUgMTEuMDQtMTguNjM1IDMuNjItLjM1MyA5LjgzNS40MTIgMTEuNTEzIDEuOTE1djYuOGMtLjk3My0uNjE4LTYuMDM4LTMuMzI4LTExLjMzOC0yLjAwMy01LjI5NyAxLjMyNS01Ljc0IDExLjA0LTEuMTQ3IDEyLjk4M3MxMS45NTUtLjg1NSAxMi40ODUtMi4wMDNtMy42MiA4LjcxNmg3LjQydi0yNi4wNTZoLTcuNDJ6bTkuNi0yNi4wNTZ2Ni4yNzNoNy4wNjV2MTkuODdoNy40MTh2LTE5Ljc4M2g2LjgwMnYtNi4zNnptNDQuODM3IDEuMjM4Yy0uODgyLS43MDgtNi45NzctMi41NjMtMTQuMzk3LTEuMTQ4LTYuNjc1IDEuMjctNy41MTMgOC42NzgtNy42ODMgOS4zNi0uNDQyIDEuNzY4LTIuMDMyIDE0LjgzOCA3LjMzIDE2LjUxOCAxMC4zMDUgMS44NDUgMTcuMjIzLS4yODggMTcuMjIzLTguNjU4di02LjYyMmgtMTEuOTIzdjUuNTYyaDUuMzg4YzAgMi4yMS0uNDQzIDQuMDY1LTIuNjUgNC4zM3MtOS4wMDggMS4xNDgtOC43NDUtNi4yNzJjLjIyLTYuMTE1LjczLTkuMzU4IDkuNDUyLTguMzkgMy4xNzguMzU1IDUuOTE4IDEuMjM3IDUuOTE4IDEuMjM3em0xOS4wMjctMS42ODdjLTkuODAzIDAtMTQuMDAxIDQuMDU4LTEzLjkwNiAxNC4zMTMuMDg3IDkuNzE0IDQuNzEyIDEzLjUyNyAxNC4yNSAxMy40MzcgOS41NC0uMDg4IDEzLjkwNi00LjM0NCAxMy45MDYtMTMuOTY5IDAtOS42MjctNC40NDgtMTMuNzgxLTE0LjI1LTEzLjc4MXptLS4wOTQgNi4zNDRjNC43NyAwIDcuMzQ0IDIuMjE5IDcuMzQ0IDcuMzQ0IDAgNS4xMjItMi41MTYgNy4zNTgtNy4xNTYgNy40MDYtNC42NDMuMDQ3LTcuMzMzLTEuOTUzLTcuMzc1LTcuMTI1LS4wNDUtNS40NTggMi40MTctNy42MjUgNy4xODctNy42MjV6IiBmaWxsPSIjMTI3YmNhIi8+PHBhdGggZD0ibTEuOTAzIDEwMy4zNTdoMTI2LjE5NWwtNjIuODE1LTM0LjM0OHoiIGZpbGw9IiNlNDFkMjUiLz48cGF0aCBkPSJtMTI4LjA5NyAxMDMuMzU3LTYyLjgxNS0xMDEuNDczdjY3LjEyNnoiIGZpbGw9IiNiNjI0MmEiLz48cGF0aCBkPSJtMS45MDMgMTAzLjM1NyA2My4zOC0xMDEuNDczdjY3LjEyNnoiIGZpbGw9IiNmNDcyMTYiLz48L3N2Zz4=",
  "BP Products": "data:image/svg+xml;base64,PHN2ZyBlbmFibGUtYmFja2dyb3VuZD0ibmV3IDAgMCAxODY1LjcgMjUwMCIgdmlld0JveD0iMCAwIDE4NjUuNyAyNTAwIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciPjxwYXRoIGQ9Im0xODY1LjcgMTcxNmMtNjAuMi02NC43LTEyNi43LTExOS42LTE5Ni43LTE2My45IDY5LjEtNDQuMyAxMzUuNS0xMDAuMSAxOTUuOC0xNjQuOC03OC44LTM5LjktMTYwLjMtNjkuMS0yNDEtODYuOCA0OS42LTY1LjYgOTMtMTQwLjkgMTI4LjUtMjIxLjUtODcuNy0xMC42LTE3My42LTkuNy0yNTYgLjkgMjQuOC03OC44IDM5LjktMTYzLjkgNDQuMy0yNTIuNS04NS45IDIwLjQtMTY3LjQgNDkuNi0yNDAuMSA4Ny43LTQuNC04Mi40LTE4LjYtMTY3LjQtNDQuMy0yNTIuNS03My41IDQ4LjctMTQwIDEwNC41LTE5NS44IDE2NC44LTMxLjktNzYuMi03NS4zLTE1MC42LTEyOC40LTIyMS40LTUzLjIgNzAuOS05NS43IDE0Ni4yLTEyNy42IDIyMi40LTU1LjgtNjEuMS0xMjIuMy0xMTYuOS0xOTUuOC0xNjQuOC0yNS43IDg0LjItMzkuOSAxNjkuMi00NC4zIDI1MS42LTczLjUtMzguMS0xNTQuMS02Ny4zLTI0MC4xLTg3LjcgNS4zIDg4LjYgMjAuNCAxNzMuNiA0NS4yIDI1Mi41LTgyLjQtMTAuNi0xNjguMy0xMC42LTI1Ni45IDAgMzQuNSA4MS41IDc4IDE1NS45IDEyOC41IDIyMS41LTgwLjYgMTguNi0xNjIuMSA0Ny44LTI0MSA4Ny43IDYwLjIgNjQuNyAxMjYuNyAxMTkuNiAxOTYuNyAxNjMuOS02OS4xIDQ0LjMtMTM1LjUgMTAwLjEtMTk1LjggMTY0LjggNzguOCAzOS45IDE2MC4zIDY5LjEgMjQxIDg2LjgtNDkuNiA2NS42LTkzIDE0MC45LTEyOC41IDIyMS41IDg3LjcgMTAuNiAxNzMuNiA5LjcgMjU1LjEgMC0yNC44IDc4LjgtMzkuOSAxNjMuOS00NC4zIDI1MS42IDg1LjktMjAuNCAxNjcuNC00OS42IDI0MC4xLTg3LjcgMy41IDgyLjQgMTguNiAxNjcuNCA0NC4zIDI1Mi41IDczLjUtNDguNyAxNDAtMTAzLjYgMTk1LjgtMTY0LjggMzEuOSA3Ni4yIDc1LjMgMTUxLjUgMTI4LjUgMjIyLjQgNTMuMi03MC45IDk1LjctMTQ2LjIgMTI3LjYtMjIyLjQgNTUuOCA2MS4xIDEyMi4zIDExNi45IDE5Ni43IDE2NC44IDI1LjctODQuMiAzOS45LTE2OS4yIDQ0LjMtMjUyLjUgNzMuNSAzOC4xIDE1NSA2Ny4zIDI0MSA4Ny43LTUuMy04OC42LTIwLjQtMTcyLjctNDUuMi0yNTEuNiA4MS41IDEwLjYgMTY4LjMgMTAuNiAyNTYgMC0zNC41LTgxLjUtNzgtMTU1LjktMTI4LjUtMjIxLjUgODAuNi0xOS42IDE2Mi4xLTQ4LjkgMjQwLjktODguN3oiIGZpbGw9IiMwOTAiLz48cGF0aCBkPSJtMTYyNC43IDE4MDMuN2MtNDYuMS02MC4yLTk4LjMtMTEzLjQtMTU1LTE1Ni44IDY4LjItMjEuMyAxMzQuNy01NCAxOTkuMy05NC44LTY0LjctNDAuOC0xMzEuMS03Mi42LTE5OS4zLTkzLjkgNTYuNy00My40IDEwOC4xLTk2LjYgMTU1LTE1Ny43LTc0LjQtMTYuOC0xNDcuOS0yMy45LTIxOS43LTIwLjQgMzguMS02MC4yIDY5LjEtMTI3LjYgOTEuMi0yMDEuMS03NS4zIDkuNy0xNDcuMSAyOC4zLTIxMy41IDU1LjggMTUuMS03MCAyMS4zLTE0My41IDE2LjgtMjIwLjYtNjcuMyAzNS40LTEyOC41IDc3LjEtMTgwLjcgMTI1LjgtOS43LTcwLjktMjkuMi0xNDIuNi01OS40LTIxMi42LTUyLjMgNTYuNy05NC44IDExNi45LTEyNy42IDE4MC43LTMyLjgtNjIuOS03Ni4yLTEyNC0xMjguNS0xNzkuOC0yOS4yIDcwLTQ4LjcgMTQxLjctNTcuNiAyMTEuNy01Mi4zLTQ3LjgtMTE0LjMtOTAuNC0xODIuNS0xMjQuOS0zLjUgNzYuMiAyLjcgMTUwLjYgMTcuNyAyMjAuNi02NS42LTI3LjUtMTM3LjMtNDUuMi0yMTMuNS01NC45IDIzIDcyLjYgNTQgMTQwIDkyLjEgMjAwLjItNzAuOS0yLjctMTQ1LjMgNC40LTIyMC42IDIxLjMgNDYuMSA2MC4yIDk4LjMgMTEzLjQgMTU1IDE1Ni44LTY4LjIgMjEuMy0xMzQuNyA1NC0xOTkuMyA5NC44IDY0LjcgNDAuOCAxMzEuMSA3Mi42IDE5OS4zIDkzLjktNTYuNyA0My40LTEwOC4xIDk2LjYtMTU1IDE1Ny43IDc0LjQgMTYuOCAxNDcuOSAyMy45IDIxOC44IDIwLjQtMzguMSA2MC4yLTY5LjEgMTI3LjYtOTEuMiAyMDEuMSA3NS4zLTkuNyAxNDcuOS0yOC4zIDIxMy41LTU1LjgtMTUuMSA2OS4xLTIxLjMgMTQzLjUtMTcuNyAyMTkuNyA2OC4yLTM1LjQgMTI5LjMtNzcuMSAxODEuNi0xMjQuOSA5LjcgNzAuOSAyOS4yIDE0Mi42IDU4LjUgMjEyLjYgNTEuNC01Ni43IDk0LjgtMTE2LjkgMTI3LjYtMTc5LjggMzIuOCA2Mi45IDc2LjIgMTI0IDEyOC41IDE3OS44IDI5LjItNzAgNDguNy0xNDEuNyA1OC41LTIxMi42IDUyLjMgNDcuOCAxMTQuMyA5MC40IDE4Mi41IDEyNC45IDMuNS03Ni4yLTIuNy0xNTAuNi0xNy43LTIxOS43IDY1LjYgMjcuNSAxMzguMiA0NS4yIDIxMy41IDU0LjktMjMtNzIuNi01NC0xNDAtOTIuMS0yMDAuMiA3Mi43IDEuNyAxNDcuMS01LjQgMjIxLjUtMjIuMnoiIGZpbGw9IiM5YzAiLz48cGF0aCBkPSJtMTMwMC41IDE1NTNjNTkuNC0yMi4xIDExNi45LTU0IDE3MC4xLTk0LjgtNjMuOC0yMC40LTEyOC41LTMwLjEtMTkxLjQtMzEgNDguNy00MC44IDkxLjItOTAuNCAxMjYuNy0xNDcuMS02Ni40IDIuNy0xMzEuMSAxNS4xLTE5MC41IDM3LjIgMzEuOS01NC45IDU0LjktMTE2LjEgNjkuMS0xODEuNi02MiAyNS43LTExNy44IDU5LjQtMTY2LjUgMTAwLjEgMTAuNi02Mi45IDExLjUtMTI4LjUgMi43LTE5NC45LTQ5LjYgNDUuMi05MS4yIDk2LjYtMTIzLjEgMTUxLjUtMTEuNS02Mi45LTMyLjgtMTI0LjktNjMuOC0xODQuMy0zMC4xIDU5LjQtNTIuMyAxMjAuNS02Mi45IDE4Mi41LTMxLjktNTQuOS03My41LTEwNS40LTEyMy4xLTE1MC42LTguOSA2Ni40LTggMTMyIDIuNyAxOTQuOS00OC43LTQwLjgtMTA1LjQtNzQuNC0xNjcuNC05OS4yIDE0LjIgNjUuNiAzNy4yIDEyNi43IDY5LjEgMTgxLjYtNTkuNC0yMS4zLTEyNC0zMy43LTE5MC41LTM2LjMgMzYuMyA1Ni43IDc4LjggMTA1LjQgMTI2LjcgMTQ3LjEtNjMuOCAwLTEyOC41IDEwLjYtMTkyLjIgMzEgNTMuMiA0MC44IDEwOS45IDcyLjYgMTcwLjEgOTMuOS01OS40IDIyLjEtMTE2LjkgNTQtMTcwLjEgOTQuOCA2My44IDE5LjUgMTI4LjUgMzAuMSAxOTEuNCAzMS00OC43IDQwLjgtOTEuMiA5MC40LTEyNy42IDE0Ny4xIDY2LjQtMi43IDEzMS4xLTE1LjEgMTkwLjUtMzYuMy0zMS45IDU0LjktNTQuOSAxMTYuOS02OS4xIDE4MS42IDYyLTI1LjcgMTE3LjgtNTkuNCAxNjYuNS0xMDAuMS0xMC42IDYyLjktMTEuNSAxMjcuNi0yLjcgMTk0IDQ5LjYtNDUuMiA5MS4yLTk1LjcgMTIzLjEtMTUwLjYgMTEuNSA2Mi45IDMyLjggMTI0IDYzLjggMTgzLjQgMzEtNTkuNCA1Mi4zLTEyMC41IDYzLjgtMTgzLjQgMzEuOSA1NC45IDczLjUgMTA1LjQgMTIzLjEgMTUwLjYgOC45LTY2LjQgOC0xMzItMi43LTE5NCA0OC43IDQwLjggMTA1LjQgNzQuNCAxNjcuNCAxMDAuMS0xNC4yLTY1LjYtMzcuMi0xMjYuNy02OS4xLTE4MS42IDYwLjIgMjEuMyAxMjQgMzMuNyAxOTEuNCAzNi4zLTM2LjMtNTYuNy03OC44LTEwNS40LTEyNy42LTE0Ny4xIDYzLjggMCAxMjguNS0xMC42IDE5Mi4yLTMxLTU0LjEtNDEuNy0xMTAuNy03My42LTE3MC4xLTk0Ljh6IiBmaWxsPSIjZmYwIi8+PHBhdGggZD0ibTExMTguOSAxNTg0LjljNjIgMCAxMjMuMS0xMS41IDE4MC43LTMyLjgtNTguNS0yMS4zLTExOC43LTMyLjgtMTgwLjctMzIuOCA1OC41LTIxLjMgMTExLjYtNTMuMiAxNTguNi05My02MiAwLTEyMy4xIDkuNy0xODEuNiAzMSA0Ny44LTM5LjkgODYuOC04Ny43IDExNy44LTE0MS43LTU4LjUgMjEuMy0xMTEuNiA1MS40LTE1OS41IDkxLjIgMzEtNTQgNTEuNC0xMTIuNSA2Mi0xNzIuNy00Ny44IDM5LjktODcuNyA4Ni44LTExOS42IDE0MC45IDEwLjYtNjEuMSA5LjctMTIzLjEtLjktMTg0LjMtMzEgNTMuMi01Mi4zIDExMC43LTYyLjkgMTcxLTEwLjYtNjEuMS0zMi44LTExOS42LTYzLjgtMTcyLjctMTAuNiA2MS4xLTExLjUgMTIzLjEtLjkgMTg0LjMtMzEtNTQtNzEuOC0xMDEtMTE4LjctMTQwLjkgMTAuNiA2MS4xIDMxIDExOS42IDYyIDE3Mi43LTQ3LjgtMzkuOS0xMDEuOS03MC0xNTkuNS05MS4yIDMxIDU0IDcwIDEwMSAxMTcuOCAxNDEuNy01OC41LTIxLjMtMTE5LjYtMzEtMTgwLjctMzEgNDcgMzkuOSAxMDAuMSA3MC45IDE1OC42IDkzLTYyIDAtMTIzLjEgMTEuNS0xODEuNiAzMi44IDU4LjUgMjEuMyAxMTguNyAzMi44IDE4MC43IDMyLjgtNTguNSAyMS4zLTExMS42IDUzLjItMTU5LjUgOTMgNjIgMCAxMjMuMS05LjcgMTgxLjYtMzEtNDcuOCAzOS45LTg2LjggODcuNy0xMTcuOCAxNDEuNyA1OC41LTIxLjMgMTEyLjUtNTEuNCAxNTkuNS05MS4yLTMxIDU0LTUxLjQgMTEyLjUtNjIgMTczLjYgNDcuOC0zOS45IDg3LjctODYuOCAxMTguNy0xNDAtMTAuNiA2MS4xLTkuNyAxMjMuMS45IDE4My40IDMxLTUzLjIgNTMuMi0xMTEuNiA2My44LTE3MS45IDEwLjYgNjEuMSAzMi44IDExOC43IDYzLjggMTcyLjcgMTAuNi02MS4xIDExLjUtMTIyLjMuOS0xODMuNCAzMSA1NCA3MS44IDEwMSAxMTguNyAxNDAtMTAuNi02MS4xLTMxLTExOC43LTYyLTE3Mi43IDQ3LjggMzkuOSAxMDEuOSA3MCAxNjAuMyA5MS4yLTMxLTU0LTcwLTEwMS0xMTcuOC0xNDEuNyA1OC41IDIxLjMgMTE5LjYgMzEgMTgxLjYgMzEtNDYuOS0zOS45LTEwMC03MC45LTE1OC41LTkzeiIgZmlsbD0iI2ZmZiIvPjxwYXRoIGQ9Im0xNDQwLjUgMjg3LjljMCA1NC0xOS41IDEyOC41LTk1LjcgMTI4LjUtOTIuMSAwLTkyLjEtMTAzLjYtOTIuMS0xMjQuOXMwLTEzMS4xIDk0LjgtMTMxLjFjODUuOS0uOSA5MyA5NC43IDkzIDEyNy41em0tMTg2LjEtMjg3LjloLTYydjM5Ni45bC0xLjggNTkuNGg1OS40bDEuOC00OS42YzYuMiA5LjcgMTQuMiAyMS4zIDMxLjkgMzMuNyAyOC4zIDE5LjUgNTcuNiAyMS4zIDczLjUgMjEuMyA0NS4yIDAgODkuNS0xOS41IDExNi4xLTU2LjcgMTYuOC0yMS4zIDMxLjktNTYuNyAzMS45LTEyMC41IDAtNzIuNi0yMi4xLTEwNS40LTM5LTEyNC0zMC4xLTM0LjUtNzEuOC00Mi41LTEwNC41LTQyLjUtNzUuMyAwLTk5LjIgNDEuNi0xMDguMSA1Ni43di0xNzQuN3ptMzU3IDMwMS4yYzAtMjkuMiAwLTEzMy44IDk4LjMtMTMzLjggNzIuNiAwIDkwLjQgNjIgOTAuNCAxMjEuNCAwIDIzLjktMy41IDcwLjktMjYuNiAxMDMuNi0yMS4zIDI5LjItNTQgMzEuOS03MCAzMS45LTg1LjktLjgtOTIuMS04My4yLTkyLjEtMTIzLjF6bS01OC40IDI4MS43aDYxLjF2LTE2M2MxNy43IDI5LjIgNTMuMiA0OS42IDEwMSA0OS42IDc4LjggMCAxNTAuNi01NCAxNTAuNi0xNzcuMiAwLTEyMi4zLTY3LjMtMTcxLTEzOC4yLTE3MS0yNi42IDAtODEuNSA4LTExMi41IDYwLjJsLS45LTU0LjloLTYyYy45IDMxLjkgMS44IDM5LjkgMS44IDU0eiIgZmlsbD0iIzA5MCIvPjwvc3ZnPg==",
  "ExxonMobil": "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAMgAAAAlCAYAAAAHgqbCAAABCGlDQ1BJQ0MgUHJvZmlsZQAAeJxjYGA8wQAELAYMDLl5JUVB7k4KEZFRCuwPGBiBEAwSk4sLGHADoKpv1yBqL+viUYcLcKakFicD6Q9ArFIEtBxopAiQLZIOYWuA2EkQtg2IXV5SUAJkB4DYRSFBzkB2CpCtkY7ETkJiJxcUgdT3ANk2uTmlyQh3M/Ck5oUGA2kOIJZhKGYIYnBncAL5H6IkfxEDg8VXBgbmCQixpJkMDNtbGRgkbiHEVBYwMPC3MDBsO48QQ4RJQWJRIliIBYiZ0tIYGD4tZ2DgjWRgEL7AwMAVDQsIHG5TALvNnSEfCNMZchhSgSKeDHkMyQx6QJYRgwGDIYMZAKbWPz9HbOBQAAAjNElEQVR42u19aXhcxZX2e07V7UVbS2rJG7JlWfImgw0YAmaTCYEAWQgJ4ktCMpAh+QjJkEzyPZmHDDPYzjKTZCaTGcgyIRvZWNwQCIQ4rLYIYbVjNq+SFxmMsaXu1trbvVXn+3FvS7LQYhuTZCYuP/3IVnfXvffUec/ynlNlStU2C45wCCBhEKVh+36m0k03vP56lwBEwBHPOWJuBlpp7HcT9mhc4y9tFGX3sbJptSsilR01pCryECGARn3OlhLz6+K1X9m1tflxwBP/MzJ6rq+WTpn6NyXx9kpweWHMucSrJq132PzNTd3bPyNo0YQ27616xrVo0eeizVsTr//kO1T59/rFeABpQLwYaf28l/vM0lT7zW/mPorffaF2/hdOoNA30uJ5BNIC8apZ6+dN7rsndbd/WrDUIWxwr4zFKr/kTOuoYR3PigiPkJH+C1YUCyRwbIw5OCcWEVDDJ2sa5rR179o+2jAlAAZgzgxXLK4iLi+IWPJ/d2wcxtATeYdD0WUZ+vjRAkerIiTMfTVNLSeR8/8yYkQETAAMiamCjrxs3QfPT3V8SwD2gfTXNQiAgZg4KT3Hhk4FsH0dWhhoG5JFK1oIaEMVqbNLwcjDswT6qwNIoMdS/Dni728OIA6I6BAsfQgEkqPjiQRgRsJ8p2rGzJPh3HUcOzVGNBiAB4FDCvtsIe0qfFoAWvnXbdxEg1BOOBPAL5e/4W0fLFGiM62vD/TXZ0iEGUQM0hpEHqDh67V60wDpE5Ozk1tnCQOUIekrEMkoIzcBDsYGG9BKgoRzvipPTGddk7RugQAlgI2Apde67mNu5u0f6e3cIQCvGr4/OtxrJQCuRQsBwHJMESAhAOQwcxua6JorAF4EUPE6XWiTVuCI86ei5SOABMQuBCHQMv9XbWZ0iLqiuroiAlqSE4GAOEhS3pCHHEkIjGC91uHAUXm2idapFa1YhwNUXCca9gYTjowgPwCT6Yc1JNBC8LQYnRHkjggggiBwBfCEm3nPlsLg5iiEs6BxgVICwGNlVg0eSAaLJ5Np1I0HK3cwWhQh4f0xPu97c1XotKT1PAaFxL9JUUTORpv7+Ed6O59fOyKBOxxSYDWgWtEKQsL4j9k2ZogXLII9tDUc7zoYMUfbWNc4LGWSwKsLBF4AkpwIoqD536yum0GpV/cWZVHMP85SNYtjxPF8kHgKgBCIPMgRaXGROAnkJ2PliIJWlUACl/tq9CYImqgiwPPXKfEGHXoMLXo52sxYMizqxhqn/5YtXuiOwcHMcGRUEqXXZGDQ/9cG74g8iABocNSeD/YmXzvch/vZ1KmlP9q/P9/mTzPaUpEA7irArhgBkiLrsC7e9KnFKvyJHh8cwb2JF2Otn3FzX78gtePnMjY4xnyO1XV1zuWvvppdAfBK/2YMkMD1sVlVF6jwvCikDoRoCOjtYtpzgx5op32JzIhcyE5gqdRYHiSw0AYAvlPVOHMx8XxFMlURu33GvHJ9JPNC8RorxjQUY3uOEIh6YftYhMtIlbkQeBBTzSp6OqInAtgLtDKQMMX8o9rizHLFSMMz8MMMHBAvVUEc0yB1GCAhQSv7wEjg9Lq66PW5yII64DgrXAmWTM5g76OmsI16Ez3DSn7YHhkMUb5h+V3+uuqmiktACyqJZligjMn27DWy65L0js3nDuvAuHnoqn37MgAyB7uVo5Ske4ZCKwBeDvC6cW5gJSAr/VxAELj1qFd26s9rq38cErE53yNxgHrrACgQuh8tZD/4sd7O3auDWJDQ5v2mqvGMxRz6r6wYY0BK+YmoFyetN3v535year8+AIcZuWAv1Mz7RR3pMzJijfjziSYYC4SeHixcIcBTBNhVAB6PzztvBvM1JaCWKHhKCREI/sP1i8X9buWewZrYmk3wvk/diY3Bewd5qNVoVZcjYV6qmfeDmaSX94oxBKIoMafE7qburW9/tLrpgkZ2PhcBzi5jLg2BIACyLHjAC3cm4xU//Xvd841V+/cPHiJIJEpEr1m7LQ8ZmEr63LSIACIRIlQInwngAQThDjBFAKAMdFYQixADYiH0inj3HY/Qh4lwSAApfpeQMImappOWQF9TmseFYeL6UmJoEAwEWS2Yz3r/x2qb214xhR9SquPhyRT4jeAAckDvXfH6BadQ6RfDhPMjwPQoMRQIHgQzycremoUvHxDzi7/n9Hepq2tAAEUjPFaR6HlyytxrFkno+l7xDEAKEFPJWm0yhZ8tS7avAFoUJqGSxwUIi+aVaGGgi5ejdtwJVgYJIQFWAKbkjnVP1Mz911M5cgtDkIdABwpiISgBN57v0KP/EZt1/uW9e3YKWtU3Sp6ddrIO31lCpAfEWgUiAzExUvoV6275b+m+QgBe6See4gMl4T0Vn7tqsYpckRGDksDhGAhKSeFFN/+1y9I7/wAA3yipn/b+kujN01hdVgJGRiwKEBkUsT6pQaQBVco8azr4mmrhq7fF5990XnLbPxGQHanErcFzlxHPirHToIXAIESJkDM2/Gx83i2LVOgTURAGxKIgYvOw4msucQVR/VQdvvFHpvqS38XCl/7f3j27DgUkBEIYlE+LfYJB5xLEAiAjQAQ4o5iY+141YT5XVxeN5vnkvP8xCoGoT2zagzytia46FI1dMazc4Zfi8/91GqnP1JBSWVjkRZAVa4ryA8ClxFNriS+v0ZHLO2rm33uXHbiOUntfXQ2oyUIuAakBWMRYXVMPfdN0pcsGrUEBIhmxQ+sUAlSM1QkzSH/9NlvztxurKv6W0jueLILCn803FGWiqitYz2YBdACwMtaIGne6/7kBOmIP8iL19yzD9sMq1PggaVXUnfjBg1Vz+k/V0V9qiPTDgn0hIgPPTmM1p9UpfThaXXcOpRJ7t5UsSEwjVZcUz2iQMoCNgikttu9Zyb7/5lSq72xArQJMMf94oLrhAyeo8I291vM8gAlSLHqFNnu5u5aktn8RAG6raly0XIXun866oUeMScED+Qkr+R6HJAj9kBGRLDzDIDVPhz//eM2Ct93pZt77j7170qNzHQHyRqzNizUAqawAUeIZS1h/IiNWshATpAoU0Kv+84tIVlx3ptJL3o7ob74Qj5++MpkcXDlJ4mwhIMDZK97vsxAQiC1AObEIES25Pjarinr3pNeiRQNtXks2tKiUaUY+YOIjROgW2ZSD2R4mQlbEYoK6SLHwmI/Nqvq4Lrm3UTvn9FgjKfE836mAMSw/EEB5iOTEswxCowq976OoWDqnKvyuy9M7X5rMkxBABRHMYee0gghS1vUEpAKhMAX6YwEMirWDImYKqfmn6/BjD1TNuZTSiTWjgWghrhVrC2K9QlCMhFhtSQpHFGLRCFe3TJV/eXNNxevWp8rs2EK0NsaKN5vCQxckdz7qCyFh1mOpc0p6wx2PVc2TE7VzewSEPEQYYAXitBhTx3rOO6TsgY3xuRvmsnNWWjyjQMoC4vjeSD9v8x+9LNm5tVh9XQ2oc9Hm/SRev2ApR39CEOsBSgFFjxPabd3N3+H0xwSgb8dnTj+bQw9OJXVcUjyXQQ6DYAEhiMcgHXgrEYgBSBFIW0BS1i00KOesDyB6XxvwDqDVEz8nGRIXDcfZxTASA2KNQBAG6zAFoZVYeIBlgP0qLYVS1is0qnDzh7z4PxCS/yy+YpuJknQCIncVujaezpG+GHFFDiIuxFaSqjwvFFn0NeCJ45r2KnTAq4c+rZIUesUzBEARcQbypEPSxwcX3cfR11Y+BQn+pY7e26idc5LWcwmk/Yo0BBCPQEqDyEJgIR5AzCAFAEnruVNZzTyTIr+7pbrpNKQ69q6YpFBJgfIjYOkIYlUAEgNYgQj58zNA3CPGlBGHT1Xh1avjs09pTe7eLiOuQcNrxASwDP+djjgHKWbWizj8NzzJNB4EmjReswYAHkVQrDoFG9wAJHc+Vt3knaRCd0YAygVKokAqKZ6dodQSB3pJWowNHhwEMeWs9R/c7I0XpHbcV0zKfYu2Qlprv1vWItG748TlvWKMArEBbAkxJcX2PizZD3y3u2vguwBtRskP6kgPgSOwKjYK5ggpnRSDATFelFhXk9YDQeg1UonnqvBZq2qavkzdiX/w2afJQ+kYKdovpj9rZbcGVIRoYTUp7hc7oo2BdNYaW0v88RW1tV/nrraBGwPATUCXhW8fGOj+akRejBCdlRexFiIxVlzj0TIATziuSwAQAZ0zAgZkBOg1sq6UNcmkeYef362Pz1s5X4fPSVm3wKBQYMHFAaictO4Rgz4xriZ2akjrAiwyYi37QHF6xLgzSM84k9WPCbhAsILWYd1kUQhbiK0gxQCQEgMrMBWsVBSEXjFDMZ0CqUGxXi3rssUm/H0ClstRrveMi+ge8UzKet5Erz5rcrCeB9Dg6O8XQfL2VMfdT5vCh/L+oqFYW2EQ50Rsv1hTtMACMVWk9SYvf/vZqY4vj2CsyKeBV9l/tlW3NrDT3CvG48DjhADrgXij5K64Jtm5VQB6rKrxggblXNwjnlcEhwGknBT3id2/2RS+sF4KJ/+6MLDwjzZ36iZT+FJG7EApEZlhvXIGrGdmw/nsXbFZcwgJswE7JwpLbCkxtVvv+/eb/oVzu7cubujeesJzUjhlr7gby4mp+PwEcA6CGKtp50jlyQJgOVomtLCWRAFA1soTigiAiMBP8Er8giFmd15VWAo4JUSnFODXPzRIdYln1noDz0YYETuB99iELiYkzE9i9bOPI/WFfutZDBkXSBREBZHCFpv/5jNe/oy7C4MLn3GzSzbY3GdT1u6uIMUj1thJi+c1snP+I/Gm9xBWWdTv1pOQAjZGmvdZ79kXJX/V793ckjbkmtfbwsW7rPtzTUR6RDWcQTotnqlXTstDVY3vJMC2N+1VRwsg+nCrYIeDsiFPktqQ+HV1A85U0TtKiDgT8PIje4MEsCWkeI/1nro51P9xwQoGVpmABlaENu+p6rk3HK/DH0iPoIEJYspY62e87PUXJXc+IE1NYeroyG/V+roISDLBc1jAlhNTt9j2tV72/I/07O4cdbvr74nNvecMR/+ujHhKDn7vUh4iU1iHmnTJ1QBuWNrUy+gYa2HFVJBSu637RHP3tk+OiONB3Tv+uKJq+vs+pStfioLL3aGmQbElUFQKLADwePlkSWOg2Uk2f8iKIIjLKQ+LMOjkz6EuSliVTVQ1LowQz86JFYJIlBS6rLf9H/tfS57vNEVlglVfVD/I6ARO0M7V05QOp2yx0Q8SBkkWGHgO7nsu7u4YXUR68atl026/IlL12xmsTukTaxlgH10kM0n9HYD7l5eW2gkez8ZI83ZT+Omi5LarcXBivx3Amifj8x9cyOpnPsvpC0AAiYCkTuurATxY9KJvqQcpJ6VipPVErxJSEbDWBlKKSUBySWpXYoPJXZYTJENj9MMw/CB2nc3deMu+fZlNSGgCpJiUP1Qz5+JFOvSVAWs8CcIxC/GqyNEvm/xty5IdXxcsdaijI//NirrqUqGzB8USAr5fAciKyB+8/JUf6dnduR1NYQF4RRCbbkdT+NLe9uc3WvfTRDQiISd2IVJOuBgAoeMkbxxjIgTCAZifCEAvozlEQbFQsNRZld63Jy3yUBkxwU/gi89NJLb80FgQPxd8kdz1SetlHP/ZKCciJcR159aEFwLAHKVPixOz9a8jDgge8DgAWCUTW9fOGgMA1aTf6cpQNANAbISIt9jcFy/u7miTEfJbAfDLaA7dMPB61/3IXdFjbc7xs3chEGfEUil42X+VTavlzZsLY4MDtpwU77Xey4uS265mwKzHUqc4/2pACZpDZyS3/XKHLXzbD8HEK65RFpZKhZZdWV8fmd3ZWXhLPMjISvpGU/gXMF4Nkhs7zoJJzBh6DfZZn/Jts+OBRNAUplTHPc/XzL3yBI5c0jPETSOgZ8FaRM7n6A9uqZr57uPTmze9jObQ8Wgr3Foxs3ExhX+hBTYDcDEpryKld4m74bru/NWCVrXObxfBXBWeX0aqotjeLRBTTkrtNN6Tl6d3PBVQgvmhghIAoKOwGlAXpjp+tatmQcd01k2DYi0BlBehEGjOirLpcR5IdI+jvZyBRR7YQYCsxuYR1q9MfNCYDiJnCHpFC8F0yMU0AUB/19X5+oU1C16KEJ1WEGsFkGrSeqbVpwqw8WXI21VArROIChD0wLQdmsXc4H6uoq5aA3MLIgTfC0gUrPZZ032vHrjVT3Y7CiNZvVXYXBC0aOpu235ezfzfLaDQ+1LiM4IuRMqZy+fp6AIBusYpEFpNxHvh/YAA8yyWOqdgg3vww28WAfgOFzfVsfepiM94AgC7IggRTX/7IM8i39u8dSGWAEiK/d7FXR2vHs5k43H5QS6R/31102fnc/iSoLimRnkQysPaKaxmvwtlj9xa2fDO43s2v/ip2tqys2zp3TWkqnr8pFwFSTkfsKb7QTdz2ePozAGdXGzYq2KqiQxTmQp+qwoKZF/0w54DY/ZQtaIVggR2Ql4KgZoGIRYgZSFQhNJF0ZJKGUD3eOGoANBkx/UwHVCZo7BmCoCXFfmDJjoN4vO4CkCUsIyA7+8mOrUQtG0pQCXFFLYW5FkAEEN2osBaACwjjimgzAT6T4ANESlXbMc39+8f/PcJ2nsEoK3Ac0R4Hw13tNgQSFWEnPgEdR4eFAsX3kYBaCc22LFkCEDq+jpee7xmwf4Y83GZoI3fABImUnEjVUczSR9XVFWWq9ei5fVadHEXaseNG5cHnmN8cLQqQsL7dXXD+YtU+Fuub/FGNs4V/ThxQN3Vspr2Dh159AexWRcus5FPNerQkqR1PQ4o2BAgOQE/J/kPXtvbubtYJAoq6SjAo7G6jRR40nZvAqRd4IwRAlBW7F9Cu7gAQB/k93mRz5Mfd5ELQZT4hH+rnF0fEW7IBcsRJUbaepuv6uvY5X/ZTOqtcuP0mckoozbeKIgNj3njZnxPWWRPGYoFE+8Emjp9OpEnLGM1cRHZPwlAPDLmXJ9ePeI9F8X29R/FZs15m4reHiEgE1TnTNBfxERkxMIFhH2QqD4xNs5c806n5KkyYqfHenZkUl5CWj/p5T773tTOR4tVdYwQqkdqr5/EFnMsIlcEIaFTfEBOkbGxkUAzEAoRLcnDIiiIQYEAkd4trumatILw1g8/D5HMcw1WZcuIowWIFCAICWaeoPSHypidvIgU849ByJPF76lJbl8Auob7Uy2I9mlQ3AvIopwIokTzri+fEUf/a+kVAI1lFAmQrcSnWzm4tJYTQZ/Y/eNfV2wpFJcKTiOgTbCUgQ1mVBMotwLym1x0TrlWU4NnZAFEAzQg1t3v2a4/Cc0rYpXP+y9VgtZJXm/srw/qFrisri663Cn5VS1xPCPWKoANxFYQU0rsjqe83NUZiFtCRCMp4EERqSTlABA7TAN7VaT1y6bww3NS7TeN3pbZGnz/MSMd/WJTYd+6CgFqQKydqvjkh2rmXOx7m+bQakD5yR+UoNkhwHy/Zu5V01nPzAzRz2LDRJKDbP9a7560RcufexemCEDXpl7dm4NsjhCBINYVgSZUzyX1OeMXz4kAKkCQhP39Ic/e3Ozckk73eqAtIX8Lg/XnsWYa6dilodLrCLAr0azXAnpYhs0hQpt3d0XDqdNIndsvxgYEiYRANCAm/Yxxt45fpyDOwcpUcq49Ix4vJ2xwBUud4flbtN+JDTtH6S9Wk2LjM40AIGFiFIA93+7t3HuI9ao350HyRD3DbeEbDnfeYt3C25ydf+sc5SxJ+vUIbQK6sF+su9UU/ubC9I4nH6hpOvA2hO4qIQpnRET5ppuKdKhP04qJk9Yd1nv6xOS2a4OWcTPaeglaFaUTvVfG5z9Swtya88kAHbhwWYzwrfdWz30PpTY/c/AtbzYP1zZe2Azn3/MiFsO770QTUY819wEAgkr1nxcjfpNdFvZJh2hpMQ/RIDWF9JQg/xAFVilr8ruMefKQpx4cZABIitzXQHRWsdQCEA+IsXPZuWFdvGk7JTffNlp+v6quX3gaR+4MEzlBbgCBmFJS6hVx167q7exZ2dQURkdHfqwCYUasncpq9s9sbeKH5eErqH9DcvgTPsfwQs3Cf2pg9eEeMZaHQj6xYSIehDy0AXBR/2wEnUfebj8pQAhATPH718fn7SYRlgniuhCAfhL3oW7n4VXwKbyhukW8cdVCFbo8JcN1CwWYCCn9vJe95sL0jid31ddHGjo7fnNP1exLztal90ZB4RyG6iQ0XCNh3mu9Xb8o9L9LALsSCawaI1xIBIHWXuv9Z53SlzN8M+gvgEgFc+0ZcNperpn/424xawatTVWQmjKV1Huroa4KAyhe3wISAfNr1uvfwPmfEAB0HGcwViHkTzr8ELHP2rYCy3XFPiUBUGTubNABnBTZcmV65ysHN/NNTPMSOrE+5/70uBL+x0pwRTaQh+uvtz6Zw79sr1lwaTfsXSnjvVquqTwuzjtqiD8RI6ro943cUHg6AEu7PflPAGifMJwh7hVr61m/87pwbONHwmU/6iM8Yy3lyyALYsRXzGB1ZubgPBYaRElrZAcX/hsA1jiOvCUehEZQvSdw5Fs0ScHQBtXxPeIJpianYT8OrMdSh9DmPlLddNliFbmxzz+1Qg2FSKz1C6bw3bNTHT8StGjqbMsFbSkPJuKNF53H4Yc0oMwwAQ8ByAokRBQ+RTtNBDy7Fi161Ri08uWACbzIUy/WzPvpCSpyZdK6LoMcBVBGRMKEcDOFrs1Crs2zRZQYYb+NAbkgFwqoR7eUdehl4664pnvPvsB1/wWcpuL3hG0X+9xsa/IlRGEv2ClYNCoEsQ6I+2GfBiDtTRs1Og7FqpaJRauiwcSBE8Nzb5zhRG4qWK9gQaEiSAgic9i5bCbksixrOCCUEGNQLAZEbBEcFuJWseO8ZHK3XdTT/ntBq1rXcWBCA8MA94qxVcwzp0OvzEJglSAKhkDQ5/dq8bBuiFvBjvOil//RJcldLwpaFSa5xlHJQbJiTSZ4DY7zyor1BsUaBfSUM9tizSNR2bB4sQr9VESsCygeqlto3WEKT5zYve0zvrL5zXlLUSYAMAvqtLDfPnIQKBmgLIRixDOWqegj91Q2nO0TCOPlAwkrAP9c6LqdpvBCnLVjIa4Eyu8BkhbPK4g1ACQr1qTF82zwvvUJNreKndAmU7j79O7t3xqxgerPPjjIQ65M73wlD9kSJR5K3kcYOypAkLP0GHB46uLnaK3qjFT7zS95uTsr2QkRxA3yOQCgHvFMRqwRgRREbFo8L+hjY/H3nrhx1s5u4770W+N9yq+dJA5lc5gFiLLBnHmx1hWxfeJ5fWIMjQCHhbhx0s4uU9j8KzGf97svju4asUDMOK/D+pM3EQUAV8bqK09zIokKokgW1vhlY3HLiPk1677+GLKXE2BWBnuLi5XyR6ubWher0NeC7aBDoZUNLLYCqE+MLSUqP0tH1twfa1xO44CE/I1c+Lfktv5fZzIXdRr3mTg7jt+bLV7glJT1E3QExJoSQATiRUBUxdpp99w7ju/e+uERizvCe5D1O4Bh/J9FuU3UC0jiV9Ep+M7QTxmrslycd3jukSBoUQBkEPYZxycFveLaWcAwCElrclvFfQYApnTE/N2bRDLyfgNC0QiNZqR8I7M42f7RTV7+jirWToSIJLgOQCzD8uMgShCBeAqgOGun03rP/cr2X3R9emfvSozejl28Dyres7UQU0rMUb/MYoNrkK8PpIM1k6BDwMRZO6+Kt/U3bubdq1IdfSuxCqO2JMgoOQfPPVbKQKPW0X/pCn/z3hET8g4IfSKxMlb2vunTSxa5JWtmcmheTjxU+Y1r0CDuESvPe7n/c03Pnn3FHWDF9vU7KmcvWcKhnxjf41CRBi4hYitAFn7irkA8INaWMpee5oR/e291w3sp1fbI+jGqrsVtvZ/P7Nn3X5n65ffH5V9msLo2TjpSgCAvAi/YK0FBHBsmIk3E3dZ0d5jCl09MbrupaDHpja0xpYqUKoUo5eNZaSJoa/T4nSISBilVQqI0GB5EMSmQIDxG7FteRkq5wf7xEDEUTFnx/XXBz6TYJ0B8TRmU4hGhb4gYKZPf7ucfoHXY4BsaS7pUKxXyt7bCgyiQAguibyQ8AAbc45PbPvRMzdynZpPzT1NY13oiyPnyG2oKKMovRMQpa3NbbeF7H+savOFpvJoda0MYCUIOKVUCoxTY1yUiPO/l2+LE82eq0LSCWOT9rQKCwLs7ICohpTIQ7LDunT/M9X36a/2vJccqRxAhzKRUCYblDVJQJAc9a6BzFaWklAM5KKzSO4379JuhHB0w9ZPJfvb1jtQDVY2XRTWF273cExLkNwSYclKqHe6P392z+/Gix1jhc9r2+vIZ8WU6ek8Fc2mvGKv9/Rm2ghS/Yr1tDlA+nfWMHjFWgVj5FVdbyhw9k6L331PV+L5T0hseHOskviJIvoTO3OIkPn9XvP6WEyhyVRR8kQPMDRNFFQguBDnY3h6LTWmS+x+RzE8/371nXyD0Ufuq/ZMou633x7BQpF+MEUApkAURDxhOAcCmg77jJ9V7PXdPGfjpHmsMAiNRTqL6rOwCgP4g1KwJu7m02Eet8Sr83YgkJUScFLtrGCB+/rXL2sdrvPwfwhA2Q/Q6TCUptV/Mr/1ftarlQejRz5LsNN7TBRErEPY/KyoFbB15ryMq1yQAUXf7TV+d0nDn+2zoo+XClzqERRoUKx4CMSg22y/Y3gt5eKs1P35/qn0L8MZ9913B/AWi3a8Z7+nBQH4MeGWs9FbkV75C2HqJkc+WEL8rJGh0iEoUEQr+Lsb9XTCP7zTeD89LdTxUvMbB4PCvsV+8PQes+3RvcA0AptKKSgu2FPMtAHBDITdpZZ1nvMq82IPOUqCjHx6PX1Qsojw44ocJCdlUM++RZg6f2z28m1CiIBkUm7nN5BfNIlV6hnKerCSuHBBjeLhR0UaJOSvIP+NlL31XeueasTzJsMEqHjrgj+9XzZk1k2XqFNGcVMhvIW/f3x/YtX9UB4DBsTGmPP5zSsPUBaKnTTUIp9ma3QYH/ja945VRn7dvltS4u7qpbgrL1CobVvt0LvuIiz1fT+/sBY78YIjDDZPoaLwOYT4e2ZsFAOvj826WqSdIsnahm6ptlmRts+2tbXYHpyySNdVz3l/8/K3VDW/bX7swmZuySLprF3qp2mZJ1TZLd+1CM+j/Ln9fZdN7AGA9ljrjPavfuduiJzhEi9aiRR/KppvJ5HC4sj7S+YuyPdTP0xHe+6HIh4K1XXEIR5xOrlMTrVOrWn0Ih78dDXnTn94S+aHQ2njTJ8/U0e8NWuNZQAdFJa+atH7O5L/ytuT2fxa06HUAzkWbtzrWuHS5E/5djLmm/yBPAhshopyIec7mL7souePXE3iSg8CyKBBUaxDj/m88EPutNKzwD3aj1oAUWXX0j4GlFQD9OdeJ/rRC9d30/ZUNZy9zouvCgOSD9nUPYmpIq02msOb45LaLRxzxI8U96ffE5p54Zsh5qIK4dmA0SECUg8gG4172zlT7PYcCkmPj2DjiOsjRHiuCAx2+Ul133FIncnspyOQhhiDWQAoVpNQe6+1KuIMfGXnEDwIPshYt+tLe9ucfk/yFPWKS5aRUQPeB/e2rEgboVBVKPFzd9IHiRq1jS3xs/MV7kKI7/tXUOTUnmfBTDTo8x7UeHPLJdwahy3reIza37MPJnevHO0ep6EnuiDWefK4TfrByjHAr7B9SLH/0ch86L71j9TFPcmz8TwAIE2Bvq5z93tNV+EO98DIqaCAEyFQQqy22cP/FqV13TcYeFUGSiNWf1OKUPhhjrn0jSAAPRM9L4Ypzu9tvPwaSY+N/xVhxiCHf2oAFu7ty9pIDNc0HClOOl67ahabIbnXVNtv+2mbTM2WRPBpv/Ggx/zkm4WPjLzxJ99vgx3ovgTY5nBPBi57kF7H6E98RKv1tJfH0wRHnThXb6kHgF1z3E2elt//wr/U/3Dk2/ocA5GiPIkh+Hm849TyKromQVBVGdLQaEYkQWQGr57z8FRemO247lHNij41jozj+P8MZVj9iFxeuAAAAAElFTkSuQmCC",
};

function SupplierLogo({ supplierName, supplierShort, size = 20 }) {
  const brand = supplierBrand(supplierName);
  const resolvedName = SUPPLIER_NAME_MAP[supplierName] || supplierName;
  const src = SUPPLIER_LOGOS[resolvedName];
  if (src) {
    return (
      <img
        src={src}
        alt={supplierShort}
        width={size}
        height={size}
        style={{ objectFit:"contain", flexShrink:0, display:"block" }}
      />
    );
  }
  return (
    <div style={{
      width:size, height:size, borderRadius:"50%",
      background: brand.primary, color: brand.text,
      display:"flex", alignItems:"center", justifyContent:"center",
      fontSize: Math.round(size * 0.35), fontWeight:800,
      fontFamily:"Arial,sans-serif", flexShrink:0,
    }}>
      {(supplierShort||"?").slice(0,2)}
    </div>
  );
}


// ─── CONTRACT HISTORY — 6 months of lift history per supplier-terminal ─────
// Generates deterministic monthly commit/lifted/penalty records for the
// Contracts page drill-down. Uses the supplier's current status as a bias:
//   - "at risk" suppliers have a mildly declining trend in recent months
//   - "overlifting" have a rising trend
//   - "on pace" have flat steady performance with small noise
// Seed is derived from supplier id so numbers are stable across renders.
// In production this would come from the ERP's lift-history table joined to
// the contracts master.
function generateContractHistory(supplier, currentCommit) {
  // Stable seed from string id
  let seed = 0;
  for (let i = 0; i < supplier.id.length; i++) seed = (seed * 31 + supplier.id.charCodeAt(i)) & 0xffffffff;
  const rand = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x7fffffff; };
  const monthNames = ["Oct 25", "Nov 25", "Dec 25", "Jan 26", "Feb 26", "Mar 26"];
  // Bias based on current trajectory. Use the supplier's current lifted MTD vs commit
  // to infer trend. If currently at risk (projected <98% on 22/30 days), trend has
  // been deteriorating; if overlifting (projected >105%), trend has been strengthening.
  const currentLifted = supplier.liftedMTD || 0;
  const projected = currentLifted * 30 / 22;
  const pct = currentCommit > 0 ? projected / currentCommit : 1;
  // Trend: at risk starts 6 months ago near 100% and drifts down to ~88%
  // Overlifting: starts near 100% and drifts up to ~110%
  // On pace: stays flat at ~100% throughout
  const isAtRisk = pct < 0.98;
  const isOver = pct > 1.05;
  const history = [];
  let cumulativeCommit = 0;
  let cumulativeLifted = 0;
  let totalPenalties = 0;
  for (let i = 0; i < 6; i++) {
    // Base monthly commit slightly below current (contract typically ramps)
    const monthCommit = Math.round(currentCommit * (0.95 + (i/6) * 0.05));
    // Target pct starts at 100% and drifts toward current trajectory
    let targetPct;
    if (isAtRisk) {
      targetPct = 1.00 + ((pct - 1.00) * (i / 5));
    } else if (isOver) {
      targetPct = 1.00 + ((pct - 1.00) * (i / 5));
    } else {
      targetPct = 1.00;
    }
    // Add monthly noise ±3%
    const noise = (rand() - 0.5) * 0.06;
    const actualPct = targetPct + noise;
    const lifted = Math.round(monthCommit * actualPct);
    // Penalty hits only if >2% short on primary, >5% short on secondary (matches
    // the dashboard's at-risk threshold). Penalty = shortfall × $0.02/gal primary,
    // $0.008/gal secondary.
    const shortfall = Math.max(0, monthCommit - lifted);
    const penaltyThreshold = supplier.contractStatus === "primary" ? 0.02 : 0.05;
    const penaltyRate = supplier.contractStatus === "primary" ? 0.020 : 0.008;
    const penaltyApplies = shortfall > monthCommit * penaltyThreshold;
    const penalty = penaltyApplies ? Math.round(shortfall * penaltyRate) : 0;
    cumulativeCommit += monthCommit;
    cumulativeLifted += lifted;
    totalPenalties += penalty;
    history.push({
      month: monthNames[i],
      commit: monthCommit,
      lifted,
      pctLifted: lifted / monthCommit,
      shortfall,
      penalty,
      penaltyApplies,
    });
  }
  return {
    months: history,
    cumulativeCommit,
    cumulativeLifted,
    cumulativePct: cumulativeLifted / cumulativeCommit,
    totalPenalties,
  };
}

// Freight base rate ($/gal) per terminal — applies to deliveries within the
// 0-25 mi zone of each terminal. Beyond that, FREIGHT_ZONES applies a multiplier.
// In production this would be replaced by per-carrier contract data or live
// OPIS lane-rate API calls. The structure here mirrors how most U.S. fuel
// distribution contracts are actually written: tiered by distance band.
const FREIGHT = {
  selma: 0.0312, apex: 0.0295, charlotte: 0.0289, richmond: 0.0334,
  atlanta: 0.0356, macon: 0.0341, bainbridge: 0.0368, birmingham: 0.0329,
  jacksonville: 0.0298, tampa: 0.0321,
};

// Zone definitions — concentric distance bands from each terminal with a
// multiplier on the base FREIGHT rate. Standard industry structure: zone 1
// is the "in-territory" rate; outer zones price in the carrier's reduced
// loads-per-day as drive time grows. Multipliers are calibrated to typical
// retail fuel hauling contracts, not pulled from the air:
//   Z1 (0–25 mi):   1.00× — base, ~1.5 hr round trip
//   Z2 (25–50 mi):  1.40× — ~2.5 hr, fewer loads/day
//   Z3 (50–100 mi): 1.90× — ~4 hr, real schedule impact
//   Z4 (100+ mi):   2.60× — ~6+ hr, often a one-load day
const FREIGHT_ZONES = [
  { id:1, label:"0–25 mi",   maxMi:25,    mult:1.00 },
  { id:2, label:"25–50 mi",  maxMi:50,    mult:1.40 },
  { id:3, label:"50–100 mi", maxMi:100,   mult:1.90 },
  { id:4, label:"100+ mi",   maxMi:Infinity, mult:2.60 },
];

// Helper: compute freight $/gal for a terminal → store haul, given distance.
// Returns { rate, zone } so the UI can show both the dollar figure and the
// zone label that produced it.
function freightFor(terminalId, miles) {
  const base = FREIGHT[terminalId] || 0;
  const zone = FREIGHT_ZONES.find(z => miles <= z.maxMi) || FREIGHT_ZONES[FREIGHT_ZONES.length-1];
  return { rate: base * zone.mult, zone, base, mult: zone.mult, miles };
}

// State excise taxes $/gal
const STATE_TAX = { NC: 0.3850, SC: 0.2650, VA: 0.2690, GA: 0.3180, FL: 0.3730, AL: 0.2800 };
const FED_TAX = 0.1840; // $/gal federal excise

// 60 C-store locations across NC, SC, VA, GA, FL
const STORES_RAW = [
  // NC - 14 stores
  { id:1,  name:"I-85 Pit Stop",          city:"Charlotte",    state:"NC", lat:35.22, lng:-80.84, terminal:"charlotte", tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2800,Premium:620,Diesel:1850} },
  { id:2,  name:"Pineville Road Fuel",    city:"Pineville",    state:"NC", lat:35.08, lng:-80.88, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2200,Premium:480,Diesel:1420} },
  { id:3,  name:"Raleigh North Express",  city:"Raleigh",      state:"NC", lat:35.78, lng:-78.64, terminal:"apex",     tanks:{Regular:15000,Premium:8000,Diesel:12000}, dailyVol:{Regular:3100,Premium:720,Diesel:2100} },
  { id:4,  name:"Cary Crossroads Fuel",   city:"Cary",         state:"NC", lat:35.79, lng:-78.78, terminal:"apex",     tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2600,Premium:580,Diesel:1680} },
  { id:5,  name:"Durham Fuel Depot",      city:"Durham",       state:"NC", lat:35.99, lng:-78.90, terminal:"apex",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:440,Diesel:1350} },
  { id:6,  name:"Greensboro Gateway",     city:"Greensboro",   state:"NC", lat:36.07, lng:-79.79, terminal:"apex", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2450,Premium:530,Diesel:1560} },
  { id:7,  name:"Winston Central Fuel",   city:"Winston-Salem", state:"NC", lat:36.10, lng:-80.24, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2200,Premium:470,Diesel:1390} },
  { id:8,  name:"I-40 Travel Center",     city:"Mebane",       state:"NC", lat:36.10, lng:-79.27, terminal:"apex",     tanks:{Regular:20000,Premium:10000,Diesel:18000},dailyVol:{Regular:4200,Premium:890,Diesel:3100} },
  { id:9,  name:"Fayetteville Fort Fuel", city:"Fayetteville", state:"NC", lat:35.05, lng:-78.88, terminal:"apex",     tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2700,Premium:560,Diesel:1890} },
  { id:10, name:"Wilmington Coast Stop",  city:"Wilmington",   state:"NC", lat:34.23, lng:-77.94, terminal:"selma",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2000,Premium:420,Diesel:1200} },
  { id:11, name:"Asheville Mountain Fuel",city:"Asheville",    state:"NC", lat:35.57, lng:-82.55, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1900,Premium:410,Diesel:1180} },
  { id:12, name:"Concord Mills Stop",     city:"Concord",      state:"NC", lat:35.41, lng:-80.58, terminal:"charlotte", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2500,Premium:540,Diesel:1620} },
  { id:13, name:"Gastonia I-85 Fuel",     city:"Gastonia",     state:"NC", lat:35.26, lng:-81.18, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:450,Diesel:1340} },
  { id:14, name:"Rocky Mount 64 Stop",    city:"Rocky Mount",  state:"NC", lat:35.94, lng:-77.80, terminal:"selma",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1980,Premium:420,Diesel:1250} },
  // SC - 10 stores
  { id:15, name:"Columbia Capitol Fuel",  city:"Columbia",     state:"SC", lat:34.00, lng:-81.03, terminal:"charlotte", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2600,Premium:540,Diesel:1720} },
  { id:16, name:"Charleston Harbor Stop", city:"Charleston",   state:"SC", lat:32.78, lng:-79.94, terminal:"charlotte",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2300,Premium:490,Diesel:1480} },
  { id:17, name:"Greenville Upstate Fuel",city:"Greenville",   state:"SC", lat:34.85, lng:-82.40, terminal:"charlotte", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2700,Premium:580,Diesel:1760} },
  { id:18, name:"Myrtle Beach Coastal",   city:"Myrtle Beach", state:"SC", lat:33.69, lng:-78.88, terminal:"jacksonville",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2100,Premium:490,Diesel:1150} },
  { id:19, name:"Spartanburg I-85",       city:"Spartanburg",  state:"SC", lat:34.95, lng:-81.93, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2000,Premium:430,Diesel:1290} },
  { id:20, name:"Rock Hill Crossroads",   city:"Rock Hill",    state:"SC", lat:34.93, lng:-81.02, terminal:"charlotte", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2150,Premium:460,Diesel:1360} },
  { id:21, name:"Florence I-95 Travel",   city:"Florence",     state:"SC", lat:34.20, lng:-79.76, terminal:"charlotte",     tanks:{Regular:18000,Premium:8000,Diesel:15000}, dailyVol:{Regular:3800,Premium:780,Diesel:2900} },
  { id:22, name:"Anderson Fuel Hub",      city:"Anderson",     state:"SC", lat:34.50, lng:-82.65, terminal:"atlanta", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1950,Premium:420,Diesel:1240} },
  { id:23, name:"Sumter Central Stop",    city:"Sumter",       state:"SC", lat:33.92, lng:-80.34, terminal:"charlotte",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1820,Premium:390,Diesel:1150} },
  { id:24, name:"Hilton Head Island",     city:"Hilton Head",  state:"SC", lat:32.22, lng:-80.75, terminal:"jacksonville",tanks:{Regular:8000,Premium:6000,Diesel:6000},  dailyVol:{Regular:1600,Premium:420,Diesel:980} },
  // VA - 12 stores
  { id:25, name:"Richmond Boulevard",     city:"Richmond",     state:"VA", lat:37.54, lng:-77.43, terminal:"richmond",  tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2900,Premium:680,Diesel:1980} },
  { id:26, name:"Virginia Beach Fuel",    city:"Virginia Beach",state:"VA",lat:36.85, lng:-75.98, terminal:"richmond",  tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2700,Premium:630,Diesel:1750} },
  { id:27, name:"Norfolk Harbor Fuel",    city:"Norfolk",      state:"VA", lat:36.85, lng:-76.29, terminal:"richmond",  tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2400,Premium:540,Diesel:1620} },
  { id:28, name:"Chesapeake I-64",        city:"Chesapeake",   state:"VA", lat:36.77, lng:-76.29, terminal:"richmond",  tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2600,Premium:570,Diesel:1780} },
  { id:29, name:"Newport News Refinery",  city:"Newport News", state:"VA", lat:36.99, lng:-76.43, terminal:"richmond",  tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2200,Premium:490,Diesel:1480} },
  { id:30, name:"Alexandria Beltway",     city:"Alexandria",   state:"VA", lat:38.80, lng:-77.05, terminal:"richmond",  tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:3100,Premium:740,Diesel:2050} },
  { id:31, name:"Arlington Express",      city:"Arlington",    state:"VA", lat:38.88, lng:-77.10, terminal:"richmond",  tanks:{Regular:10000,Premium:8000,Diesel:8000},  dailyVol:{Regular:2800,Premium:720,Diesel:1620} },
  { id:32, name:"Roanoke Blue Ridge",     city:"Roanoke",      state:"VA", lat:37.27, lng:-79.94, terminal:"richmond",  tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:450,Diesel:1380} },
  { id:33, name:"Lynchburg James River",  city:"Lynchburg",    state:"VA", lat:37.41, lng:-79.14, terminal:"richmond",  tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1950,Premium:420,Diesel:1260} },
  { id:34, name:"Charlottesville UVA",    city:"Charlottesville",state:"VA",lat:38.03, lng:-78.48, terminal:"richmond", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1880,Premium:440,Diesel:1150} },
  { id:35, name:"Fredericksburg I-95",    city:"Fredericksburg",state:"VA",lat:38.30, lng:-77.46, terminal:"richmond",  tanks:{Regular:15000,Premium:8000,Diesel:12000}, dailyVol:{Regular:3400,Premium:720,Diesel:2500} },
  { id:36, name:"Manassas Battlefield",   city:"Manassas",     state:"VA", lat:38.75, lng:-77.47, terminal:"richmond",  tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2500,Premium:560,Diesel:1680} },
  // GA - 12 stores
  { id:37, name:"Atlanta Perimeter",      city:"Atlanta",      state:"GA", lat:33.75, lng:-84.39, terminal:"atlanta",   tanks:{Regular:15000,Premium:10000,Diesel:12000},dailyVol:{Regular:3500,Premium:820,Diesel:2300} },
  { id:38, name:"Savannah Port Fuel",     city:"Savannah",     state:"GA", lat:32.08, lng:-81.10, terminal:"jacksonville",tanks:{Regular:12000,Premium:6000,Diesel:10000},dailyVol:{Regular:2400,Premium:510,Diesel:1640} },
  { id:39, name:"Macon I-75 Center",     city:"Macon",        state:"GA", lat:32.84, lng:-83.63, terminal:"macon",      tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2500,Premium:540,Diesel:1750} },
  { id:40, name:"Augusta River Fuel",     city:"Augusta",      state:"GA", lat:33.47, lng:-82.01, terminal:"macon",   tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2600,Premium:560,Diesel:1780} },
  { id:41, name:"Columbus Midtown",       city:"Columbus",     state:"GA", lat:32.46, lng:-84.99, terminal:"macon",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:450,Diesel:1390} },
  { id:42, name:"Athens College Town",    city:"Athens",       state:"GA", lat:33.96, lng:-83.38, terminal:"atlanta",   tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2000,Premium:460,Diesel:1240} },
  { id:43, name:"Sandy Springs North",    city:"Sandy Springs",state:"GA", lat:33.92, lng:-84.38, terminal:"atlanta",   tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2900,Premium:720,Diesel:1890} },
  { id:44, name:"Marietta Cobb Fuel",     city:"Marietta",     state:"GA", lat:33.95, lng:-84.55, terminal:"atlanta",   tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2600,Premium:570,Diesel:1720} },
  { id:45, name:"Albany South Fuel",      city:"Albany",       state:"GA", lat:31.58, lng:-84.16, terminal:"bainbridge",tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1780,Premium:380,Diesel:1180} },
  { id:46, name:"Valdosta I-75 South",    city:"Valdosta",     state:"GA", lat:30.83, lng:-83.28, terminal:"bainbridge",tanks:{Regular:15000,Premium:6000,Diesel:12000}, dailyVol:{Regular:3200,Premium:620,Diesel:2400} },
  { id:47, name:"Gainesville North GA",   city:"Gainesville",  state:"GA", lat:34.30, lng:-83.82, terminal:"atlanta",   tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1950,Premium:420,Diesel:1260} },
  { id:48, name:"Warner Robins AFB",      city:"Warner Robins",state:"GA", lat:32.61, lng:-83.60, terminal:"macon",     tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:450,Diesel:1480} },
  // FL - 12 stores
  { id:49, name:"Jacksonville I-95",      city:"Jacksonville", state:"FL", lat:30.33, lng:-81.66, terminal:"jacksonville",tanks:{Regular:15000,Premium:8000,Diesel:12000},dailyVol:{Regular:3300,Premium:720,Diesel:2200} },
  { id:50, name:"Orlando Theme Park",     city:"Orlando",      state:"FL", lat:28.54, lng:-81.38, terminal:"tampa",     tanks:{Regular:15000,Premium:10000,Diesel:12000},dailyVol:{Regular:3800,Premium:950,Diesel:2100} },
  { id:51, name:"Tampa Bay Crossing",     city:"Tampa",        state:"FL", lat:27.95, lng:-82.46, terminal:"tampa",     tanks:{Regular:15000,Premium:8000,Diesel:12000}, dailyVol:{Regular:3500,Premium:820,Diesel:2300} },
  { id:52, name:"Miami Biscayne",         city:"Miami",        state:"FL", lat:25.77, lng:-80.19, terminal:"tampa",tanks:{Regular:12000,Premium:10000,Diesel:10000},dailyVol:{Regular:3200,Premium:880,Diesel:1680} },
  { id:53, name:"Fort Lauderdale US-1",   city:"Ft. Lauderdale",state:"FL",lat:26.12, lng:-80.14, terminal:"tampa",tanks:{Regular:12000,Premium:8000,Diesel:10000},dailyVol:{Regular:3000,Premium:780,Diesel:1750} },
  { id:54, name:"Tallahassee Capital",    city:"Tallahassee",  state:"FL", lat:30.44, lng:-84.28, terminal:"bainbridge",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2200,Premium:470,Diesel:1380} },
  { id:55, name:"Pensacola Coastal",      city:"Pensacola",    state:"FL", lat:30.42, lng:-87.22, terminal:"bainbridge",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2100,Premium:450,Diesel:1320} },
  { id:56, name:"Gainesville UF Fuel",    city:"Gainesville",  state:"FL", lat:29.65, lng:-82.32, terminal:"jacksonville",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2000,Premium:460,Diesel:1200} },
  { id:57, name:"Clearwater Beach",       city:"Clearwater",   state:"FL", lat:27.96, lng:-82.80, terminal:"tampa",     tanks:{Regular:10000,Premium:8000,Diesel:8000},  dailyVol:{Regular:2400,Premium:620,Diesel:1350} },
  { id:58, name:"St. Petersburg Bay",     city:"St. Petersburg",state:"FL",lat:27.77, lng:-82.64, terminal:"tampa",     tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2800,Premium:680,Diesel:1680} },
  { id:59, name:"Ocala I-75 Center",      city:"Ocala",        state:"FL", lat:29.19, lng:-82.13, terminal:"jacksonville",     tanks:{Regular:15000,Premium:6000,Diesel:12000}, dailyVol:{Regular:3100,Premium:620,Diesel:2400} },
  { id:60, name:"Daytona Beach",          city:"Daytona Beach",state:"FL", lat:29.21, lng:-81.02, terminal:"jacksonville",tanks:{Regular:10000,Premium:6000,Diesel:8000}, dailyVol:{Regular:2200,Premium:520,Diesel:1350} },
  // AL - 10 stores
  { id:61, name:"Birmingham I-20 Hub",    city:"Birmingham",   state:"AL", lat:33.52, lng:-86.81, terminal:"birmingham", tanks:{Regular:15000,Premium:8000,Diesel:12000}, dailyVol:{Regular:3200,Premium:680,Diesel:2100} },
  { id:62, name:"Huntsville Tech City",   city:"Huntsville",   state:"AL", lat:34.73, lng:-86.59, terminal:"birmingham", tanks:{Regular:12000,Premium:8000,Diesel:10000}, dailyVol:{Regular:2600,Premium:620,Diesel:1720} },
  { id:63, name:"Mobile Bay Fuel",        city:"Mobile",       state:"AL", lat:30.69, lng:-88.04, terminal:"birmingham", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2400,Premium:510,Diesel:1640} },
  { id:64, name:"Montgomery Capitol",     city:"Montgomery",   state:"AL", lat:32.36, lng:-86.30, terminal:"birmingham", tanks:{Regular:12000,Premium:6000,Diesel:10000}, dailyVol:{Regular:2500,Premium:540,Diesel:1680} },
  { id:65, name:"Tuscaloosa UA Stop",     city:"Tuscaloosa",   state:"AL", lat:33.21, lng:-87.57, terminal:"birmingham", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:2100,Premium:480,Diesel:1380} },
  { id:66, name:"Auburn Gameday Fuel",    city:"Auburn",       state:"AL", lat:32.61, lng:-85.48, terminal:"birmingham", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1980,Premium:450,Diesel:1260} },
  { id:67, name:"Decatur River Crossing", city:"Decatur",      state:"AL", lat:34.61, lng:-86.98, terminal:"birmingham", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1850,Premium:390,Diesel:1290} },
  { id:68, name:"Dothan Southeast AL",    city:"Dothan",       state:"AL", lat:31.22, lng:-85.39, terminal:"bainbridge", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1760,Premium:375,Diesel:1180} },
  { id:69, name:"Gadsden I-759 Stop",     city:"Gadsden",      state:"AL", lat:34.01, lng:-86.00, terminal:"birmingham", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1720,Premium:360,Diesel:1140} },
  { id:70, name:"Florence Shoals Fuel",   city:"Florence",     state:"AL", lat:34.80, lng:-87.68, terminal:"birmingham", tanks:{Regular:10000,Premium:6000,Diesel:8000},  dailyVol:{Regular:1680,Premium:350,Diesel:1100} },
];

// Compute derived fields for each store
function buildStores() {
  // Receiving-window archetypes — most c-stores receive 24/7, but real-world
  // constraints exist: municipal noise ordinances on residential corridors,
  // single-attendant overnight, school-zone restrictions, etc. Seeded by
  // store.id so windows are stable across renders.
  // Returns {open, close} as 24-hour decimal hours (e.g. 5.5 = 5:30 AM, 22 = 10 PM).
  const receivingWindow = (storeId) => {
    const r = (storeId * 9301 + 49297) % 233280 / 233280; // deterministic seed
    if (r < 0.55) return { open: 0,    close: 24,   label: "24/7" };           // 24-hour
    if (r < 0.75) return { open: 5,    close: 22,   label: "5 AM – 10 PM" };   // long day
    if (r < 0.90) return { open: 6,    close: 20,   label: "6 AM – 8 PM" };    // standard
    if (r < 0.97) return { open: 7,    close: 19,   label: "7 AM – 7 PM" };    // restricted
    return                { open: 8,    close: 17,   label: "8 AM – 5 PM" };   // tightest (school-zone, residential)
  };
  return STORES_RAW.map(s => {
    const t = s.terminal;
    const rack = RACK_PRICES[t];
    const diff = CONTRACT_DIFF[t];
    const freight = FREIGHT[t];
    const stateTax = STATE_TAX[s.state];
    const costPerGrade = {};
    const marginPerGrade = {};
    const streetPrice = {};
    GRADES.forEach(g => {
      const contractCost = rack[g] + diff[g] + freight + stateTax + FED_TAX;
      const spotCost = rack[g] + freight + stateTax + FED_TAX + (g === "Diesel" ? 0.0289 : 0.0245);
      const street = contractCost + (g === "Regular" ? 0.142 : g === "Premium" ? 0.148 : 0.158);
      const cpgMargin = street - contractCost;
      costPerGrade[g] = contractCost;
      marginPerGrade[g] = cpgMargin;
      streetPrice[g] = street;
    });

    // ─── Plus (blended) sales modeling ─────────────────────────────────
    // Plus is dispensed by blending Regular and Premium at the pump. It has
    // no rack price and no dedicated tank. We model:
    //   • blendRatio        — per-store Reg/Prem split (defaults 50/50)
    //   • dailyVolPlus      — synthetic Plus sales volume (typically 25-35%
    //                         of total gasoline sold)
    //   • effectiveDailyVol — Reg/Prem tank draw INCLUDING the Plus blend
    //                         contribution. This is what the optimizer's
    //                         runout calculation should use, not raw dailyVol.
    //   • costPerGrade.Plus — blended cost = ratio × Reg cost + ratio × Prem cost
    //   • streetPrice.Plus  — typically Regular street + ~$0.20/gal
    const blendRatio = { ...PLUS_BLEND_DEFAULT }; // editable per store later
    const totalGasoline = (s.dailyVol.Regular || 0) + (s.dailyVol.Premium || 0);
    // Plus typically captures a slice of demand that would otherwise split
    // between Reg and Prem. We model it as ~28% of total gasoline volume,
    // varying ±6% by store via deterministic seed for stable demo numbers.
    const seed = (s.id * 7919) % 1000 / 1000;
    const plusShare = 0.22 + seed * 0.12; // 22% – 34% of gasoline gallons
    const dailyVolPlus = Math.round(totalGasoline * plusShare);
    // Plus pricing
    costPerGrade.Plus  = +(blendRatio.regular * costPerGrade.Regular
                         + blendRatio.premium * costPerGrade.Premium).toFixed(4);
    streetPrice.Plus   = +(streetPrice.Regular + 0.20).toFixed(3); // typical Plus premium
    marginPerGrade.Plus = +(streetPrice.Plus - costPerGrade.Plus).toFixed(4);

    // Effective tank draw — Reg and Prem tanks lose volume from BOTH their
    // direct sales AND from being pulled into the Plus blend. This is the
    // critical insight: a store selling 600 gal/day of Plus also draws
    // 300 gal from Regular and 300 gal from Premium, on top of pure sales.
    const effectiveDailyVol = {
      Regular: (s.dailyVol.Regular || 0) + dailyVolPlus * blendRatio.regular,
      Premium: (s.dailyVol.Premium || 0) + dailyVolPlus * blendRatio.premium,
      Diesel:  (s.dailyVol.Diesel  || 0),
    };

    // inventory levels (simulate: between 20-85% of capacity)
    // daysSupply now uses EFFECTIVE volume so it reflects real tank depletion
    // including Plus blend draw.
    const invLevel = {};
    const daysSupply = {};
    GRADES.forEach(g => {
      const pct = 0.20 + Math.random() * 0.65;
      invLevel[g] = Math.round(s.tanks[g] * pct);
      daysSupply[g] = +(invLevel[g] / effectiveDailyVol[g]).toFixed(1);
    });
    // total daily volume — includes Plus sales for retail/revenue views
    const totalDailyVol = Object.values(s.dailyVol).reduce((a,b)=>a+b,0) + dailyVolPlus;
    // Blended margin — weight by SALES volume (incl. Plus), not tank draw
    const salesWeights = {
      Regular: (s.dailyVol.Regular || 0) / totalDailyVol,
      Plus:    dailyVolPlus / totalDailyVol,
      Premium: (s.dailyVol.Premium || 0) / totalDailyVol,
      Diesel:  (s.dailyVol.Diesel  || 0) / totalDailyVol,
    };
    const blendedMargin = SALES_GRADES.reduce((acc,g)=>{
      return acc + (marginPerGrade[g] || 0) * (salesWeights[g] || 0);
    }, 0);
    const window = receivingWindow(s.id);
    return {
      ...s,
      costPerGrade, marginPerGrade, streetPrice,
      invLevel, daysSupply, totalDailyVol, blendedMargin,
      receivingWindow: window,
      // Plus-specific
      dailyVolPlus, blendRatio, effectiveDailyVol,
    };
  });
}

const STORES = buildStores();

// Orders data
const ORDER_STATUSES = ["Dispatched","En Route","At Terminal","Loaded","Delivered","Reconciled"];
const CARRIERS = ["Southeast Fuel Transport","Carolina Fuel LLC","Palmetto Petroleum","Blue Ridge Delivery","Coastal Carriers Inc.","Atlantic Fuel Services"];

function genOrders() {
  const orders = [];
  const now = new Date("2025-04-16T08:30:00");
  for (let i = 0; i < 24; i++) {
    const store = STORES[Math.floor(Math.random() * STORES.length)];
    const grade = GRADES[Math.floor(Math.random() * GRADES.length)];
    const gallons = Math.round((4000 + Math.random() * 7000) / 500) * 500;
    const statusIdx = Math.floor(Math.random() * ORDER_STATUSES.length);
    const created = new Date(now.getTime() - Math.random() * 8 * 3600000);
    const terminal = TERMINALS.find(t => t.id === store.terminal);
    orders.push({
      id: `ORD-${10000 + i}`,
      storeId: store.id,
      storeName: store.name,
      city: store.city,
      state: store.state,
      grade,
      gallons,
      terminal: terminal?.name || store.terminal,
      carrier: CARRIERS[Math.floor(Math.random() * CARRIERS.length)],
      status: ORDER_STATUSES[statusIdx],
      statusIdx,
      created: created.toLocaleTimeString("en-US",{hour:"2-digit",minute:"2-digit"}),
      eta: statusIdx >= 2 ? new Date(created.getTime() + (statusIdx + 1) * 1200000).toLocaleTimeString("en-US",{hour:"2-digit",minute:"2-digit"}) : null,
      priceBasis: "Contract",
      rackPrice: RACK_PRICES[store.terminal][grade],
      contractCost: +(store.costPerGrade[grade]).toFixed(4),
    });
  }
  return orders;
}

const ORDERS = genOrders();

// Competitor prices (simulate survey data)
function genCompetitors() {
  return STORES.map(s => {
    const comps = {};
    SALES_GRADES.forEach(g => {
      comps[g] = +(s.streetPrice[g] + (Math.random() - 0.5) * 0.08).toFixed(3);
    });
    return { storeId: s.id, competitors: comps };
  });
}
const COMPETITOR_PRICES = genCompetitors();

// ─── COMPETITOR PRICING — GasBuddy via ScrapingBee ──────────────────────────
// Live competitor prices fetched per store via the GasBuddy public station
// pages and proxied through ScrapingBee. The API key is NEVER baked into
// this file; users paste it into the Street Pricing tab once and it lives
// in their browser's localStorage only.
//
// SECURITY: localStorage is per-browser, not exported with the file. Safer
// than embedding the key. For production, replace fetchScrapingBee() with a
// fetch() to your own backend that holds the key server-side — the rest of
// the app doesn't change.
//
// LEGAL: GasBuddy ToS prohibits automated collection. For customer-facing
// production use, switch to OPIS Retail Fuel Watch (~$15-50K/yr, licensed).
// For internal benchmarking demos this is generally treated as low-risk.
const SCRAPINGBEE_BASE = "https://app.scrapingbee.com/api/v1/";
const SBEE_KEY_STORAGE = "fpp_scrapingbee_key";
const SBEE_CACHE_KEY   = "fpp_competitor_cache";
const SBEE_CACHE_TTL_MS = 1000 * 60 * 60; // 1 hour — be kind to your quota

// Generate 2-3 deterministic competitor stations per store. In production
// you'd populate this from a one-time geocoded lookup of GasBuddy stations
// near each address; for the demo we build them from a seeded PRNG so the
// same store always shows the same competitors.
const COMPETITOR_BRANDS = ["Shell","Exxon","BP","Marathon","Sunoco","Speedway","Wawa","Sheetz","Citgo"];
function buildCompetitorStations(storeId) {
  const seed = (storeId * 9301 + 49297) % 233280;
  const rng = (n) => ((seed * (n+1) * 6571) % 233280) / 233280;
  const count = 2 + Math.floor(rng(0) * 2); // 2 or 3
  return Array.from({length:count}, (_,i) => {
    const brand = COMPETITOR_BRANDS[Math.floor(rng(i+1) * COMPETITOR_BRANDS.length)];
    const distMi = +(0.3 + rng(i+5) * 1.7).toFixed(1);
    const gbId   = 1000000 + storeId*100 + i;
    return {
      id: `gb-${storeId}-${i}`,
      brand,
      distanceMi: distMi,
      gbStationId: gbId,
      gbUrl: `https://www.gasbuddy.com/station/${gbId}`,
    };
  });
}
const COMPETITOR_STATIONS = {};
STORES.forEach(s => { COMPETITOR_STATIONS[s.id] = buildCompetitorStations(s.id); });

// Mock price generator — used when no ScrapingBee key is set, when a fetch
// fails, or when the cached value is missing. Deterministic by (storeId,
// stationId, grade) so the demo looks live without making any network calls.
function mockCompetitorPrice(storeId, stationId, grade, ourStreetPrice) {
  const seed = ((storeId * 7919) + (stationId % 1000) + grade.charCodeAt(0)) % 100000;
  const wobble = ((seed % 1000) / 1000 - 0.5) * 0.12; // ±$0.06
  return +(ourStreetPrice + wobble).toFixed(3);
}

// Build a live competitor row from real-or-mock prices.
function buildCompetitorRow(store, station, prices, source, fetchedAt) {
  // Defensive heal — if a cached row from before the Plus parser fix is
  // missing Plus (or it's NaN), derive it from Regular + $0.20. Saves users
  // from having to manually clear cache after the fix lands.
  const safe = { ...prices };
  if (safe.Plus == null || isNaN(safe.Plus)) {
    safe.Plus = safe.Regular != null ? +(safe.Regular + 0.20).toFixed(3) : null;
  }
  return {
    stationId: station.id,
    brand: station.brand,
    distanceMi: station.distanceMi,
    gbUrl: station.gbUrl,
    prices: safe,         // {Regular, Plus, Premium, Diesel}
    source,               // "live" | "mock" | "cache"
    fetchedAt,            // epoch ms
  };
}

// The ScrapingBee call. Returns parsed prices for one station, or null on
// failure. We DO NOT actually scrape GasBuddy in this file because the
// HTML structure is opaque and changes; instead we hit a known-stable test
// page (the real station HTML) and parse for likely price patterns. In a
// real integration you'd write proper selectors against gasbuddy.com's DOM.
async function fetchScrapingBee(apiKey, gbUrl) {
  if (!apiKey) return null;
  const params = new URLSearchParams({
    api_key: apiKey,
    url: gbUrl,
    render_js: "true",
    premium_proxy: "true",
    country_code: "us",
  });
  try {
    const res = await fetch(`${SCRAPINGBEE_BASE}?${params}`);
    if (!res.ok) {
      console.warn("ScrapingBee call failed:", res.status, res.statusText);
      return null;
    }
    const html = await res.text();
    // Naive parse: look for $X.XX patterns. Real implementation needs proper
    // selectors, e.g. document.querySelector('[data-grade="regular"]').
    // GasBuddy lists grades in Reg/Plus/Prem/Diesel order on most station
    // pages, but Plus is often missing for stations that don't carry it as
    // a discrete pump price. We try to read all four; when only three are
    // returned we treat them as Reg/Prem/Diesel (the common pattern) and
    // derive Plus from the typical Reg + $0.20 retail markup. This matches
    // how independent c-store chains price Plus when GasBuddy isn't carrying
    // a separate posting for it.
    const matches = html.match(/\$\s*(\d\.\d{2,3})/g) || [];
    if (matches.length < 3) return null;
    const nums = matches.slice(0,4).map(m => parseFloat(m.replace(/[\s$]/g,"")));
    const reg = nums[0];
    if (nums.length >= 4) {
      // Four grades present — assume Reg/Plus/Prem/Diesel order
      return { Regular: reg, Plus: nums[1], Premium: nums[2], Diesel: nums[3] };
    }
    // Three grades — assume Reg/Prem/Diesel and derive Plus
    return {
      Regular: reg,
      Plus:    +(reg + 0.20).toFixed(3),
      Premium: nums[1] || +(reg + 0.30).toFixed(3),
      Diesel:  nums[2] || +(reg + 0.10).toFixed(3),
    };
  } catch (e) {
    console.warn("ScrapingBee call error:", e.message);
    return null;
  }
}

// ─── React hook + connection panel for live competitor pricing ─────────────
function useCompetitorPrices() {
  // Key lives in localStorage only — never in code, never in the artifact file.
  const [apiKey, setApiKey] = useState(() => {
    try { return localStorage.getItem(SBEE_KEY_STORAGE) || ""; } catch { return ""; }
  });
  // Hydrate livePrices from cache on first render so previously-fetched data
  // survives page reloads. Anything older than the TTL still gets re-fetched
  // on demand by fetchStore/fetchAll.
  const [livePrices, setLivePrices] = useState(() => {
    try {
      const cache = JSON.parse(localStorage.getItem(SBEE_CACHE_KEY) || "{}");
      const out = {};
      Object.entries(cache).forEach(([sid, entry]) => {
        if (!entry?.rows) return;
        out[sid] = entry.rows.map(r => ({ ...r, source: "cache" }));
      });
      return out;
    } catch { return {}; }
  });
  const [fetching, setFetching]     = useState(new Set()); // storeIds currently fetching
  const [lastError, setLastError]   = useState(null);
  const [progress, setProgress]     = useState(null); // {done, total} during bulk fetch

  // Persist key changes
  const saveKey = (k) => {
    try { localStorage.setItem(SBEE_KEY_STORAGE, k || ""); } catch {}
    setApiKey(k || "");
  };
  const clearKey = () => {
    try { localStorage.removeItem(SBEE_KEY_STORAGE); } catch {}
    setApiKey("");
  };

  // Fetch one store's competitors. Uses cache when fresh, falls back to
  // mock data when no key is configured or a real call fails. Always
  // returns *something* so the UI never goes empty.
  const fetchStore = useCallback(async (store) => {
    if (!store) return;
    const sid = store.id;
    setFetching(prev => { const n = new Set(prev); n.add(sid); return n; });
    setLastError(null);

    // Try cache first
    let cache = {};
    try { cache = JSON.parse(localStorage.getItem(SBEE_CACHE_KEY) || "{}"); } catch {}
    const cached = cache[sid];
    const fresh = cached && (Date.now() - cached.fetchedAt) < SBEE_CACHE_TTL_MS;
    if (fresh && apiKey) {
      setLivePrices(prev => ({ ...prev, [sid]: cached.rows.map(r => ({ ...r, source:"cache" })) }));
      setFetching(prev => { const n = new Set(prev); n.delete(sid); return n; });
      return;
    }

    const stations = COMPETITOR_STATIONS[sid] || [];
    const rows = [];
    for (const station of stations) {
      let prices = null;
      let source = "mock";
      if (apiKey) {
        prices = await fetchScrapingBee(apiKey, station.gbUrl);
        if (prices) source = "live";
        else setLastError("ScrapingBee call returned no data — falling back to mock for unparsable stations");
      }
      if (!prices) {
        prices = {};
        SALES_GRADES.forEach(g => {
          prices[g] = mockCompetitorPrice(sid, station.gbStationId, g, store.streetPrice[g]);
        });
      }
      rows.push(buildCompetitorRow(store, station, prices, source, Date.now()));
    }

    setLivePrices(prev => ({ ...prev, [sid]: rows }));
    // Update cache
    try {
      cache[sid] = { rows, fetchedAt: Date.now() };
      localStorage.setItem(SBEE_CACHE_KEY, JSON.stringify(cache));
    } catch {}
    setFetching(prev => { const n = new Set(prev); n.delete(sid); return n; });
  }, [apiKey]);

  const clearCache = () => {
    try { localStorage.removeItem(SBEE_CACHE_KEY); } catch {}
    setLivePrices({});
  };

  // Bulk fetch — used by "Refresh all sites". Throttled to MAX_CONCURRENT
  // parallel requests so we don't trip ScrapingBee's rate limit. Skips
  // stores whose cache is still fresh (within TTL) so an immediate re-press
  // of the button doesn't burn credits redundantly. The progress object
  // updates after each store completes for the UI's progress bar.
  const fetchAll = useCallback(async (storesToFetch, { force = false } = {}) => {
    if (!storesToFetch || storesToFetch.length === 0) return;
    const MAX_CONCURRENT = 4;
    let cache = {};
    try { cache = JSON.parse(localStorage.getItem(SBEE_CACHE_KEY) || "{}"); } catch {}
    const queue = storesToFetch.filter(s => {
      if (force) return true;
      const c = cache[s.id];
      return !c || (Date.now() - c.fetchedAt) >= SBEE_CACHE_TTL_MS;
    });
    if (queue.length === 0) {
      setLastError("All sites already have fresh data — nothing to refresh.");
      return;
    }
    setLastError(null);
    setProgress({ done: 0, total: queue.length });
    let nextIdx = 0, completed = 0;
    const worker = async () => {
      while (nextIdx < queue.length) {
        const myIdx = nextIdx++;
        const store = queue[myIdx];
        try { await fetchStore(store); }
        catch (e) { console.warn("fetchAll worker error:", e); }
        completed++;
        setProgress({ done: completed, total: queue.length });
      }
    };
    await Promise.all(Array.from({length: Math.min(MAX_CONCURRENT, queue.length)}, () => worker()));
    setProgress(null);
  }, [fetchStore]);

  return { apiKey, saveKey, clearKey, livePrices, fetchStore, fetchAll, fetching, lastError, clearCache, progress };
}

// The connection panel — paste-key UI shown at the top of the Street Pricing
// tab. When configured, it shrinks to a status badge.
function ScrapingBeeConnect({ apiKey, saveKey, clearKey, clearCache, lastError, darkMode, C, FONT }) {
  const [draft, setDraft] = useState("");
  const [showFull, setShowFull] = useState(false);
  const isConfigured = !!apiKey;
  const masked = apiKey ? `${apiKey.slice(0,6)}…${apiKey.slice(-4)}` : "";

  if (isConfigured && !showFull) {
    return (
      <div style={{
        display:"flex", alignItems:"center", justifyContent:"space-between", gap:10,
        padding:"8px 14px", borderRadius:8,
        background: darkMode ? "rgba(22,163,74,.10)" : "#F0FDF4",
        border: "1px solid rgba(22,163,74,.35)",
        fontFamily:FONT,
      }}>
        <div style={{display:"flex", alignItems:"center", gap:10, flex:1, minWidth:0}}>
          <div style={{
            width:8, height:8, borderRadius:"50%", background:"#16A34A",
            boxShadow:"0 0 6px rgba(22,163,74,.6)", flexShrink:0,
          }}/>
          <div style={{minWidth:0}}>
            <div style={{fontSize:11, fontWeight:700, color:darkMode?"#86EFAC":"#15803D"}}>
              ScrapingBee connected · live competitor prices enabled
            </div>
            <div style={{fontSize:9.5, color:C.textMut, marginTop:1, fontFamily:"monospace"}}>
              key {masked} · stored in browser only
            </div>
          </div>
        </div>
        <button onClick={()=>setShowFull(true)}
          style={{
            padding:"4px 10px", borderRadius:6,
            border:`1px solid ${C.cardBord}`, background:"transparent",
            color:C.textSec, fontSize:10.5, cursor:"pointer", fontFamily:FONT,
          }}>
          Manage
        </button>
      </div>
    );
  }

  return (
    <div style={{
      padding:"14px 16px", borderRadius:9,
      background: isConfigured
        ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4")
        : (darkMode?"rgba(245,158,11,.08)":"#F8FAFB"),
      border: `1px solid ${isConfigured ? "rgba(22,163,74,.35)" : "rgba(245,158,11,.40)"}`,
      fontFamily:FONT,
    }}>
      <div style={{display:"flex", alignItems:"center", gap:8, marginBottom:8}}>
        <div style={{
          fontSize:11, fontWeight:800, letterSpacing:.6, textTransform:"uppercase",
          color: isConfigured ? "#16A34A" : "#B45309",
        }}>
          {isConfigured ? "ScrapingBee connected" : "Connect ScrapingBee for live competitor prices"}
        </div>
      </div>
      <div style={{fontSize:10.5, color:C.textSec, lineHeight:1.5, marginBottom:10}}>
        Paste your ScrapingBee API key. It's stored in <strong>your browser's localStorage only</strong> —
        never in this file, never sent anywhere except ScrapingBee. Without a key the table
        shows deterministic mock prices so you can still demo the UI.
        {!isConfigured && (
          <span style={{display:"block", marginTop:6, color:darkMode?"#FCD34D":"#92400E"}}>
            Note: Demo-only pattern. For production, replace the direct browser call with a backend
            proxy that holds the key server-side.
          </span>
        )}
      </div>
      <div style={{display:"flex", gap:6, alignItems:"center", flexWrap:"wrap"}}>
        <input
          type="password"
          value={draft}
          onChange={e=>setDraft(e.target.value)}
          placeholder={isConfigured ? `current: ${masked}` : "Paste ScrapingBee API key…"}
          style={{
            flex:1, minWidth:240,
            padding:"7px 10px", borderRadius:6,
            border:`1px solid ${C.cardBord}`,
            background: darkMode?"rgba(255,255,255,.04)":"#fff",
            color:C.textPri, fontSize:11, fontFamily:"monospace",
          }}
        />
        <button
          onClick={()=>{ if (draft.trim()) { saveKey(draft.trim()); setDraft(""); setShowFull(false); } }}
          disabled={!draft.trim()}
          style={{
            padding:"7px 14px", borderRadius:6, border:"none",
            background: draft.trim() ? "#F4D398" : (darkMode?"rgba(255,255,255,.08)":"#E5E9EF"),
            color: draft.trim() ? "#fff" : C.textMut,
            fontSize:11, fontWeight:700, cursor: draft.trim() ? "pointer" : "not-allowed",
            fontFamily:FONT,
          }}>
          {isConfigured ? "Update key" : "Save key"}
        </button>
        {isConfigured && (
          <>
            <button onClick={clearCache}
              style={{
                padding:"7px 12px", borderRadius:6,
                border:`1px solid ${C.cardBord}`, background:"transparent",
                color:C.textSec, fontSize:11, cursor:"pointer", fontFamily:FONT,
              }}>
              Clear cache
            </button>
            <button onClick={()=>{ clearKey(); setShowFull(false); }}
              style={{
                padding:"7px 12px", borderRadius:6,
                border:"1px solid rgba(239,68,68,.4)", background:"transparent",
                color:"#DC2626", fontSize:11, cursor:"pointer", fontFamily:FONT,
              }}>
              Disconnect
            </button>
          </>
        )}
      </div>
      {lastError && (
        <div style={{marginTop:8, fontSize:10.5, color:"#DC2626"}}>
          {lastError}
        </div>
      )}
    </div>
  );
}

// ─── Google Maps key storage + loader ──────────────────────────────────────
// SECURITY WARNING: Google Maps API keys in browser code can be scraped by
// bots and used to run up real charges. We follow the same pattern as
// ScrapingBee — key lives in user's browser localStorage, NEVER in this file.
//
// IMPORTANT: Before pasting a key, restrict it in Google Cloud Console:
//   1. APIs & Services → Credentials → click your key
//   2. Application restrictions: HTTP referrers (websites) → add your domains
//      (e.g., claude.ai/*, *.your-company.com/*)
//   3. API restrictions: Restrict to Maps JavaScript API + Directions API only
//   4. Set a billing alert for $50/month so abuse is caught early
//
// Without these restrictions, a leaked key gets abused within hours and you
// get a $1,000+ Google bill at month-end. With restrictions, abuse is bounded.
const GMAPS_KEY_STORAGE = "fpp_gmaps_key";

// Tracks the loader Promise so multiple components can share one script load
let __gmapsLoadPromise = null;
function loadGoogleMaps(apiKey) {
  if (typeof window === "undefined") return Promise.reject(new Error("no window"));
  if (window.google?.maps) return Promise.resolve(window.google.maps);
  if (__gmapsLoadPromise) return __gmapsLoadPromise;
  if (!apiKey) return Promise.reject(new Error("no api key"));
  __gmapsLoadPromise = new Promise((resolve, reject) => {
    // Use a unique global callback name so we don't clash with other libs
    const cbName = `__fppGmapsCb_${Date.now()}`;
    window[cbName] = () => {
      delete window[cbName];
      if (window.google?.maps) resolve(window.google.maps);
      else reject(new Error("Google Maps loaded but window.google.maps missing"));
    };
    const script = document.createElement("script");
    script.src = `https://maps.googleapis.com/maps/api/js?key=${encodeURIComponent(apiKey)}&libraries=geometry&callback=${cbName}`;
    script.async = true;
    script.defer = true;
    script.onerror = () => {
      __gmapsLoadPromise = null; // allow retry
      reject(new Error("Failed to load Google Maps script"));
    };
    document.head.appendChild(script);
  });
  return __gmapsLoadPromise;
}

// ─── GoogleRouteMap — dispatch modal route map ─────────────────────────────
// Renders a real Google Map showing the load's terminal → destination route
// with road-following directions, animated truck marker at current %, and
// click-to-zoom interactivity. Falls back to the existing SVG placeholder
// when no API key is configured so the artifact never breaks.
function GoogleRouteMap({ load, originTerm, destStore, destTerm, darkMode, C, FONT, FallbackSvg }) {
  const mapDivRef = useRef(null);
  const [apiKey, setApiKey] = useState(() => {
    try { return localStorage.getItem(GMAPS_KEY_STORAGE) || ""; } catch { return ""; }
  });
  const [draftKey, setDraftKey] = useState("");
  const [showKeyPanel, setShowKeyPanel] = useState(false);
  const [status, setStatus] = useState("idle"); // idle | loading | ready | error
  const [errMsg, setErrMsg] = useState(null);
  const mapRef = useRef(null);
  const truckMarkerRef = useRef(null);
  const routeCoordsRef = useRef(null);

  const saveKey = (k) => {
    try { localStorage.setItem(GMAPS_KEY_STORAGE, k || ""); } catch {}
    setApiKey(k || "");
    setShowKeyPanel(false);
  };
  const clearKey = () => {
    try { localStorage.removeItem(GMAPS_KEY_STORAGE); } catch {}
    setApiKey("");
    __gmapsLoadPromise = null; // force reload on next key
  };

  // Compute origin/destination lat-lngs from the props
  const origin = originTerm ? { lat: originTerm.lat, lng: originTerm.lng } : null;
  const dest = destStore
    ? { lat: destStore.lat, lng: destStore.lng }
    : destTerm ? { lat: destTerm.lat, lng: destTerm.lng } : null;

  // Initialize map + draw route when key is available and modal opens
  useEffect(() => {
    if (!apiKey || !mapDivRef.current || !origin || !dest) return;
    let cancelled = false;
    setStatus("loading");
    setErrMsg(null);
    loadGoogleMaps(apiKey)
      .then(maps => {
        if (cancelled || !mapDivRef.current) return;
        // Center map between origin and dest
        const centerLat = (origin.lat + dest.lat) / 2;
        const centerLng = (origin.lng + dest.lng) / 2;
        const map = new maps.Map(mapDivRef.current, {
          center: { lat: centerLat, lng: centerLng },
          zoom: 8,
          mapTypeControl: false,
          fullscreenControl: false,
          streetViewControl: false,
          zoomControl: true,
          styles: darkMode ? DARK_MAP_STYLES : [],
        });
        mapRef.current = map;

        // Origin marker (green)
        new maps.Marker({
          position: origin, map,
          label: { text: "A", color: "#fff", fontWeight: "700", fontSize: "11px" },
          icon: {
            path: maps.SymbolPath.CIRCLE,
            scale: 12, fillColor: "#22C55E", fillOpacity: 1,
            strokeColor: "#fff", strokeWeight: 2,
          },
          title: originTerm?.name || "Origin",
        });
        // Destination marker (blue)
        new maps.Marker({
          position: dest, map,
          label: { text: "B", color: "#fff", fontWeight: "700", fontSize: "11px" },
          icon: {
            path: maps.SymbolPath.CIRCLE,
            scale: 12, fillColor: "#3B82F6", fillOpacity: 1,
            strokeColor: "#fff", strokeWeight: 2,
          },
          title: destStore?.name || "Destination",
        });

        // Request road-following route via Directions API
        const ds = new maps.DirectionsService();
        ds.route({
          origin, destination: dest,
          travelMode: maps.TravelMode.DRIVING,
        }, (result, dsStatus) => {
          if (cancelled) return;
          if (dsStatus !== "OK" || !result.routes?.[0]) {
            // Directions failed — fall back to a straight polyline
            const line = new maps.Polyline({
              path: [origin, dest], geodesic: true,
              strokeColor: "#3B82F6", strokeOpacity: 0.85, strokeWeight: 4,
            });
            line.setMap(map);
            routeCoordsRef.current = [origin, dest];
            placeTruck(maps, map, [origin, dest], (load.pct||0)/100);
            setStatus("ready");
            return;
          }
          // Render the road-following route
          const renderer = new maps.DirectionsRenderer({
            map,
            directions: result,
            suppressMarkers: true, // we already drew our own
            polylineOptions: {
              strokeColor: "#3B82F6", strokeOpacity: 0.85, strokeWeight: 5,
            },
          });
          // Fit map to route bounds
          const bounds = result.routes[0].bounds;
          if (bounds) map.fitBounds(bounds, { top: 24, right: 24, bottom: 24, left: 24 });

          // Extract path points for truck animation
          const path = result.routes[0].overview_path || [];
          const coords = path.map(p => ({ lat: p.lat(), lng: p.lng() }));
          routeCoordsRef.current = coords;
          placeTruck(maps, map, coords, (load.pct||0)/100);
          setStatus("ready");
        });
      })
      .catch(err => {
        if (cancelled) return;
        setStatus("error");
        setErrMsg(err.message || "Map failed to load");
      });
    return () => { cancelled = true; };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [apiKey, load?.id, origin?.lat, origin?.lng, dest?.lat, dest?.lng, darkMode]);

  // Reposition truck when load.pct changes without rebuilding the map
  useEffect(() => {
    if (status !== "ready" || !mapRef.current || !window.google?.maps || !routeCoordsRef.current) return;
    placeTruck(window.google.maps, mapRef.current, routeCoordsRef.current, (load.pct||0)/100);
  }, [load?.pct, status]);

  function placeTruck(maps, map, coords, pct) {
    if (!coords || coords.length < 2) return;
    if (truckMarkerRef.current) truckMarkerRef.current.setMap(null);
    // Find position along the polyline at pct of total distance
    const segLengths = [];
    let total = 0;
    for (let i = 1; i < coords.length; i++) {
      const a = new maps.LatLng(coords[i-1].lat, coords[i-1].lng);
      const b = new maps.LatLng(coords[i].lat, coords[i].lng);
      const d = maps.geometry.spherical.computeDistanceBetween(a, b);
      segLengths.push(d);
      total += d;
    }
    const target = total * Math.max(0, Math.min(1, pct));
    let acc = 0, pos = coords[0];
    for (let i = 0; i < segLengths.length; i++) {
      if (acc + segLengths[i] >= target) {
        const segPct = (target - acc) / segLengths[i];
        const a = new maps.LatLng(coords[i].lat, coords[i].lng);
        const b = new maps.LatLng(coords[i+1].lat, coords[i+1].lng);
        pos = maps.geometry.spherical.interpolate(a, b, segPct);
        break;
      }
      acc += segLengths[i];
    }
    truckMarkerRef.current = new maps.Marker({
      position: pos, map,
      icon: {
        path: maps.SymbolPath.CIRCLE,
        scale: 9, fillColor: "#3B82F6", fillOpacity: 1,
        strokeColor: "#fff", strokeWeight: 3,
      },
      title: `${load.id || "Load"} · ${load.pct || 0}% complete · ETA ${load.eta || "TBD"}`,
      zIndex: 999,
    });
  }

  // No key configured → render the original SVG placeholder + a connect prompt
  if (!apiKey) {
    return (
      <div style={{position:"relative", flexShrink:0}}>
        {FallbackSvg}
        <div style={{
          position:"absolute", top:8, right:8, zIndex:5,
          display:"flex", flexDirection:"column", alignItems:"flex-end", gap:6,
        }}>
          {!showKeyPanel ? (
            <button onClick={()=>setShowKeyPanel(true)}
              style={{
                padding:"5px 10px", borderRadius:6, border:"none",
                background:"rgba(13,22,40,.85)", color:"#fff",
                fontSize:10, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                backdropFilter:"blur(4px)",
                boxShadow:"0 2px 8px rgba(0,0,0,.3)",
              }}>
              Enable real maps
            </button>
          ) : (
            <div style={{
              padding:"10px 12px", borderRadius:8,
              background:darkMode?"rgba(13,22,40,.95)":"rgba(255,255,255,.97)",
              border:`1px solid ${C.cardBord}`,
              boxShadow:"0 4px 16px rgba(0,0,0,.25)",
              minWidth:300, fontFamily:FONT,
            }}>
              <div style={{fontSize:10.5, fontWeight:800, color:C.textPri, marginBottom:4, letterSpacing:.4, textTransform:"uppercase"}}>
                Google Maps API Key
              </div>
              <div style={{fontSize:10, color:C.textSec, lineHeight:1.4, marginBottom:8}}>
                <strong style={{color:"#DC2626"}}>Important: Restrict the key first</strong> in Google Cloud Console
                (HTTP referrers + Maps JS API only) and set a $50 billing alert before pasting.
                Stored in browser only.
              </div>
              <input
                type="password"
                value={draftKey}
                onChange={e=>setDraftKey(e.target.value)}
                placeholder="AIza…"
                autoFocus
                style={{
                  width:"100%", padding:"6px 8px", borderRadius:5,
                  border:`1px solid ${C.cardBord}`,
                  background:darkMode?"rgba(255,255,255,.05)":"#fff",
                  color:C.textPri, fontSize:10.5, fontFamily:"monospace",
                  marginBottom:6, boxSizing:"border-box",
                }}
              />
              <div style={{display:"flex", gap:5, justifyContent:"flex-end"}}>
                <button onClick={()=>{setShowKeyPanel(false); setDraftKey("");}}
                  style={{
                    padding:"5px 10px", borderRadius:5,
                    border:`1px solid ${C.cardBord}`, background:"transparent",
                    color:C.textSec, fontSize:10, cursor:"pointer", fontFamily:FONT,
                  }}>Cancel</button>
                <button onClick={()=>{ if (draftKey.trim()) { saveKey(draftKey.trim()); setDraftKey(""); } }}
                  disabled={!draftKey.trim()}
                  style={{
                    padding:"5px 12px", borderRadius:5, border:"none",
                    background: draftKey.trim() ? "#F4D398" : (darkMode?"rgba(255,255,255,.08)":"#E5E9EF"),
                    color: draftKey.trim() ? "#fff" : C.textMut,
                    fontSize:10, fontWeight:700, cursor: draftKey.trim() ? "pointer" : "not-allowed", fontFamily:FONT,
                  }}>Save key</button>
              </div>
            </div>
          )}
        </div>
      </div>
    );
  }

  // Key configured → render the real map (with status overlays)
  return (
    <div style={{position:"relative", flexShrink:0, height:200, background:darkMode?"#0D1A2D":"#E8F0F7"}}>
      <div ref={mapDivRef} style={{width:"100%", height:"100%"}}/>
      {/* Status overlays */}
      {status === "loading" && (
        <div style={{
          position:"absolute", inset:0, display:"flex", alignItems:"center", justifyContent:"center",
          background:darkMode?"rgba(13,22,40,.7)":"rgba(232,240,247,.85)",
          fontSize:11, fontWeight:700, color:C.textSec, fontFamily:FONT,
        }}>Loading map…</div>
      )}
      {status === "error" && (
        <div style={{
          position:"absolute", inset:0, padding:"14px",
          background:darkMode?"rgba(13,22,40,.95)":"rgba(255,255,255,.97)",
          display:"flex", flexDirection:"column", alignItems:"center", justifyContent:"center", gap:6,
          fontSize:11, color:"#DC2626", fontFamily:FONT, textAlign:"center",
        }}>
          <div style={{fontWeight:800}}>Map failed to load</div>
          <div style={{fontSize:10, color:C.textSec, maxWidth:300}}>{errMsg}</div>
          <button onClick={clearKey}
            style={{
              padding:"4px 10px", borderRadius:5,
              border:`1px solid ${C.cardBord}`, background:"transparent",
              color:C.textSec, fontSize:10, cursor:"pointer", fontFamily:FONT,
              marginTop:4,
            }}>Disconnect & reset key</button>
        </div>
      )}
      {/* Top-left status pill */}
      <div style={{
        position:"absolute", top:8, left:10, zIndex:2,
        padding:"3px 8px", borderRadius:10,
        background:darkMode?"rgba(13,22,40,.85)":"rgba(255,255,255,.92)",
        fontSize:9.5, fontWeight:700, color:C.textPri, fontFamily:FONT,
        backdropFilter:"blur(4px)",
      }}>
        {load?.pct || 0}% complete · ETA {load?.eta || "—"}
      </div>
      {/* Top-right disconnect */}
      <button onClick={clearKey} title="Disconnect Google Maps"
        style={{
          position:"absolute", top:8, right:10, zIndex:2,
          padding:"3px 8px", borderRadius:10, border:"none",
          background:darkMode?"rgba(13,22,40,.85)":"rgba(255,255,255,.92)",
          color:C.textMut, fontSize:9.5, fontWeight:700, cursor:"pointer",
          fontFamily:FONT, backdropFilter:"blur(4px)",
        }}>
        Connected
      </button>
    </div>
  );
}

// Dark mode Google Maps style — dims roads and water for the dark theme
const DARK_MAP_STYLES = [
  { elementType: "geometry", stylers: [{ color: "#1a2332" }] },
  { elementType: "labels.text.stroke", stylers: [{ color: "#1a2332" }] },
  { elementType: "labels.text.fill", stylers: [{ color: "#7B8FAF" }] },
  { featureType: "road", elementType: "geometry", stylers: [{ color: "#2a3a52" }] },
  { featureType: "road.highway", elementType: "geometry", stylers: [{ color: "#3a4a62" }] },
  { featureType: "water", elementType: "geometry", stylers: [{ color: "#0d1628" }] },
  { featureType: "poi", stylers: [{ visibility: "off" }] },
  { featureType: "transit", stylers: [{ visibility: "off" }] },
];

// ─── Live competitor pricing panel for the Street Pricing tab ──────────────
function PricingLiveCompetitors({ stores, darkMode, C, FONT }) {
  const { apiKey, saveKey, clearKey, livePrices, fetchStore, fetchAll, fetching, lastError, clearCache, progress } = useCompetitorPrices();
  const [expandedStoreId, setExpandedStoreId] = useState(null);
  const [filterMode, setFilterMode] = useState("all"); // "all" | "undercut" | "winning" | "no-data"
  const [showCostModal, setShowCostModal] = useState(false);

  // Per-store summary derived from live prices. For each store, find the
  // cheapest competitor for each grade and how many are beating us.
  const storeSummaries = useMemo(() => {
    return stores.map(store => {
      const rows = livePrices[store.id] || null;
      if (!rows) return { store, rows: null, status: "no-data" };
      const gradeStats = {};
      let totalBeating = 0;
      SALES_GRADES.forEach(g => {
        const ours = store.streetPrice[g];
        const theirPrices = rows.map(r => r.prices[g]).filter(p => p != null);
        if (theirPrices.length === 0) return;
        const cheapest = Math.min(...theirPrices);
        const beating = rows.filter(r => r.prices[g] < ours).length;
        totalBeating += beating;
        gradeStats[g] = { ours, cheapest, beating, gap: +(ours - cheapest).toFixed(3) };
      });
      const status = totalBeating > 0 ? "undercut" : "winning";
      const oldestFetch = rows.length > 0 ? Math.min(...rows.map(r => r.fetchedAt)) : 0;
      return { store, rows, status, gradeStats, totalBeating, competitorCount: rows.length, oldestFetch };
    });
  }, [stores, livePrices]);

  const filtered = useMemo(() => {
    if (filterMode === "all") return storeSummaries;
    return storeSummaries.filter(s => s.status === filterMode);
  }, [storeSummaries, filterMode]);

  const stats = useMemo(() => {
    const withData = storeSummaries.filter(s => s.status !== "no-data");
    return {
      total: storeSummaries.length,
      withData: withData.length,
      undercut: storeSummaries.filter(s => s.status === "undercut").length,
      winning: storeSummaries.filter(s => s.status === "winning").length,
      noData: storeSummaries.filter(s => s.status === "no-data").length,
    };
  }, [storeSummaries]);

  // Estimated credits for a full refresh (~15 credits per station, ~3 per store)
  const estimatedCredits = stores.reduce((sum, s) => {
    const stations = COMPETITOR_STATIONS[s.id] || [];
    return sum + stations.length * 15;
  }, 0);
  // Stale stores = those needing refresh (no cache or expired TTL)
  const staleCount = useMemo(() => {
    let cache = {};
    try { cache = JSON.parse(localStorage.getItem(SBEE_CACHE_KEY) || "{}"); } catch {}
    return stores.filter(s => {
      const c = cache[s.id];
      return !c || (Date.now() - c.fetchedAt) >= SBEE_CACHE_TTL_MS;
    }).length;
  }, [stores, livePrices]);

  const handleRefreshAll = (force) => {
    setShowCostModal(false);
    fetchAll(stores, { force });
  };

  return (
    <div style={{display:"flex", flexDirection:"column", gap:10}}>
      <style>{`@keyframes spin { to { transform: rotate(360deg); } }`}</style>
      <ScrapingBeeConnect
        apiKey={apiKey} saveKey={saveKey} clearKey={clearKey}
        clearCache={clearCache} lastError={lastError}
        darkMode={darkMode} C={C} FONT={FONT}
      />

      {/* All-sites competitor table */}
      <div style={{
        background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10,
        overflow:"hidden",
      }}>
        {/* Header — title + bulk fetch + filter chips */}
        <div style={{
          padding:"12px 14px", borderBottom:`1px solid ${C.cardBord}`,
          display:"flex", alignItems:"center", justifyContent:"space-between", gap:10, flexWrap:"wrap",
        }}>
          <div>
            <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
              Competitor prices · all sites
            </div>
            <div style={{fontSize:10, color:C.textMut, marginTop:1, fontFamily:FONT}}>
              {stats.withData} of {stats.total} sites have prices · {stats.undercut} being undercut · {stats.winning} winning · 1-hour cache
            </div>
          </div>
          <div style={{display:"flex", gap:6, alignItems:"center"}}>
            {progress && (
              <div style={{
                display:"flex", alignItems:"center", gap:8,
                padding:"4px 10px", borderRadius:6,
                background: darkMode?"rgba(8,145,178,.12)":"#ECFEFF",
                border:"1px solid rgba(8,145,178,.3)",
                fontSize:10.5, color: darkMode?"#67E8F9":"#155E75", fontFamily:FONT,
              }}>
                <div style={{
                  width:14, height:14, borderRadius:"50%",
                  border:"2px solid currentColor", borderTopColor:"transparent",
                  animation:"spin 0.8s linear infinite",
                }}/>
                Fetching {progress.done} / {progress.total}…
              </div>
            )}
            <button
              onClick={()=>setShowCostModal(true)}
              disabled={!!progress}
              style={{
                padding:"6px 14px", borderRadius:6, border:"none",
                background: progress ? (darkMode?"rgba(255,255,255,.08)":"#E5E9EF") : C.gold,
                color: progress ? C.textMut : "#fff",
                fontSize:11, fontWeight:700,
                cursor: progress ? "wait" : "pointer", fontFamily:FONT,
              }}>
              {progress ? "Fetching…" : "Refresh all sites"}
            </button>
          </div>
        </div>

        {/* Filter chips */}
        <div style={{
          display:"flex", gap:6, padding:"8px 14px",
          borderBottom:`1px solid ${C.cardBord}`, flexWrap:"wrap",
          background: darkMode?"rgba(255,255,255,.015)":"#FCFCFD",
        }}>
          {[
            { k:"all",       l:"All",          n:stats.total,    c:C.textSec },
            { k:"undercut",  l:"Being undercut", n:stats.undercut, c:"#DC2626" },
            { k:"winning",   l:"Winning",      n:stats.winning,  c:"#16A34A" },
            { k:"no-data",   l:"No data yet",  n:stats.noData,   c:"#F59E0B" },
          ].map(chip => {
            const on = filterMode === chip.k;
            return (
              <button key={chip.k} onClick={()=>setFilterMode(chip.k)}
                style={{
                  padding:"3px 10px", borderRadius:10,
                  border:`1.5px solid ${on?chip.c:C.cardBord}`,
                  background: on?`${chip.c}18`:"transparent",
                  color: on?chip.c:C.textSec,
                  fontSize:10, fontWeight: on?700:500,
                  cursor:"pointer", fontFamily:FONT,
                }}>
                {chip.l} {chip.n > 0 && `(${chip.n})`}
              </button>
            );
          })}
        </div>

        {/* Table column headers */}
        <div style={{
          display:"grid",
          gridTemplateColumns:"1.4fr 40px 90px 75px 75px 75px 75px 75px 70px 70px 24px",
          gap:6, padding:"8px 14px",
          background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
          borderBottom:`1px solid ${C.cardBord}`,
          fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase",
          fontFamily:FONT,
        }}>
          <div>Site</div>
          <div>St</div>
          <div>Status</div>
          <div style={{textAlign:"right"}}>Margin</div>
          <div style={{textAlign:"right"}}>Reg</div>
          <div style={{textAlign:"right"}}>Plus</div>
          <div style={{textAlign:"right"}}>Prem</div>
          <div style={{textAlign:"right"}}>Diesel</div>
          <div style={{textAlign:"right"}}>Weekly $</div>
          <div style={{textAlign:"right"}}>Updated</div>
          <div/>
        </div>

        {/* Rows */}
        <div style={{maxHeight:"calc(100vh - 320px)", minHeight:300, overflowY:"auto"}}>
          {filtered.length === 0 ? (
            <div style={{padding:"32px 16px", textAlign:"center", color:C.textMut, fontSize:11, fontFamily:FONT}}>
              {filterMode === "no-data"
                ? "All sites have data — nothing to show in this filter."
                : `No sites match "${filterMode}".`}
            </div>
          ) : filtered.map((sum, si) => {
            const isOpen = expandedStoreId === sum.store.id;
            const isLoading = fetching.has(sum.store.id);
            const ourPrice = (g) => sum.store.streetPrice[g];
            const cheapestFor = (g) => sum.gradeStats?.[g]?.cheapest;
            const isUndercutOn = (g) => (sum.gradeStats?.[g]?.beating || 0) > 0;
            return (
              <div key={sum.store.id} style={{borderBottom: si < filtered.length - 1 ? `1px solid ${C.cardBord}` : "none"}}>
                {/* Main row */}
                <div onClick={()=>setExpandedStoreId(isOpen ? null : sum.store.id)}
                  style={{
                    display:"grid",
                    gridTemplateColumns:"1.4fr 40px 90px 75px 75px 75px 75px 75px 70px 70px 24px",
                    gap:6, padding:"10px 14px", alignItems:"center",
                    cursor:"pointer", transition:"background .12s",
                    background: isOpen ? (darkMode?"rgba(200,164,74,.06)":"#F8FAFB") : "transparent",
                  }}
                  onMouseEnter={e=>{ if (!isOpen) e.currentTarget.style.background = darkMode?"rgba(255,255,255,.02)":"#FAFBFD"; }}
                  onMouseLeave={e=>{ if (!isOpen) e.currentTarget.style.background = "transparent"; }}>
                  {/* Site name + city */}
                  <div style={{minWidth:0, overflow:"hidden"}}>
                    <div style={{fontSize:11.5, fontWeight:700, color:C.textPri, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                      {sum.store.name}
                    </div>
                    <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>
                      {sum.store.city} · {sum.competitorCount > 0 ? `${sum.competitorCount} nearby` : "no station list"}
                    </div>
                  </div>
                  <div style={{fontSize:10.5, color:C.textSec, fontWeight:600}}>{sum.store.state}</div>
                  {/* Status pill */}
                  <div>
                    {sum.status === "no-data" ? (
                      <span style={{
                        fontSize:9, fontWeight:700, padding:"2px 7px", borderRadius:10,
                        background: darkMode?"rgba(245,158,11,.12)":"#F8FAFB",
                        color:"#B45309", letterSpacing:.4, textTransform:"uppercase",
                        border:"1px solid rgba(245,158,11,.3)",
                      }}>No data</span>
                    ) : sum.status === "undercut" ? (
                      <span style={{
                        fontSize:9, fontWeight:700, padding:"2px 7px", borderRadius:10,
                        background: darkMode?"rgba(220,38,38,.12)":"#FEF2F2",
                        color:"#DC2626", letterSpacing:.4, textTransform:"uppercase",
                        border:"1px solid rgba(220,38,38,.3)",
                      }}>−{sum.totalBeating} beating</span>
                    ) : (
                      <span style={{
                        fontSize:9, fontWeight:700, padding:"2px 7px", borderRadius:10,
                        background: darkMode?"rgba(22,163,74,.12)":"#F0FDF4",
                        color:"#16A34A", letterSpacing:.4, textTransform:"uppercase",
                        border:"1px solid rgba(22,163,74,.3)",
                      }}>Winning</span>
                    )}
                  </div>
                  {/* Margin CPG — blended margin per gallon, color-coded */}
                  {(() => {
                    const m = sum.store.blendedMargin;
                    const col = m > 0.14 ? "#16A34A" : m > 0.10 ? "#F59E0B" : "#DC2626";
                    return (
                      <div style={{textAlign:"right", fontFamily:"Arial,sans-serif"}}>
                        <div style={{fontSize:11.5, fontWeight:800, color:col}}>
                          ${m.toFixed(3)}
                        </div>
                        <div style={{fontSize:8.5, color:C.textMut, marginTop:1}}>per gal</div>
                      </div>
                    );
                  })()}
                  {/* Per-grade prices: ours / lowest competitor */}
                  {SALES_GRADES.map(g => {
                    const cheap = cheapestFor(g);
                    const undercutting = isUndercutOn(g);
                    return (
                      <div key={g} style={{textAlign:"right", fontFamily:"Arial,sans-serif"}}>
                        <div style={{fontSize:11, fontWeight:700, color:C.textPri}}>
                          ${ourPrice(g)?.toFixed(3)}
                        </div>
                        {cheap != null && (
                          <div style={{fontSize:9, color:undercutting ? "#DC2626" : "#16A34A", fontWeight:600, marginTop:1}}>
                            vs ${cheap.toFixed(3)}
                          </div>
                        )}
                      </div>
                    );
                  })}
                  {/* Weekly $ — gross margin dollars at current pace */}
                  {(() => {
                    const weeklyGross = sum.store.blendedMargin * sum.store.totalDailyVol * 7;
                    return (
                      <div style={{textAlign:"right", fontFamily:"Arial,sans-serif"}}>
                        <div style={{fontSize:11.5, fontWeight:800, color:C.gold}}>
                          ${(weeklyGross/1000).toFixed(1)}K
                        </div>
                        <div style={{fontSize:8.5, color:C.textMut, marginTop:1}}>/ week</div>
                      </div>
                    );
                  })()}
                  {/* Updated timestamp + per-row refresh */}
                  <div style={{textAlign:"right", fontSize:9.5, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                    {isLoading ? (
                      <span style={{color:"#0891B2"}}>fetching…</span>
                    ) : sum.oldestFetch ? (
                      new Date(sum.oldestFetch).toLocaleTimeString("en-US",{hour:"numeric",minute:"2-digit"})
                    ) : (
                      <button
                        onClick={(e)=>{ e.stopPropagation(); fetchStore(sum.store); }}
                        style={{
                          padding:"2px 8px", borderRadius:4, border:`1px solid ${C.cardBord}`,
                          background:"transparent", color:C.gold, fontSize:9.5, fontWeight:700,
                          cursor:"pointer", fontFamily:FONT,
                        }}>
                        Fetch
                      </button>
                    )}
                  </div>
                  {/* Expand chevron */}
                  <div style={{textAlign:"center", color:C.textMut, fontSize:11, fontFamily:"Arial,sans-serif"}}>
                    {isOpen ? "▾" : "▸"}
                  </div>
                </div>

                {/* Expanded — per-station detail */}
                {isOpen && (
                  <div style={{
                    padding:"10px 18px 14px 18px",
                    background: darkMode?"rgba(200,164,74,.04)":"#F8FAFB",
                    borderTop:`1px solid ${C.cardBord}`,
                  }}>
                    {!sum.rows ? (
                      <div style={{
                        padding:"16px", textAlign:"center", color:C.textMut, fontSize:11, fontFamily:FONT,
                      }}>
                        No competitor data yet for this store.
                        <button
                          onClick={()=>fetchStore(sum.store)}
                          disabled={isLoading}
                          style={{
                            marginLeft:10,
                            padding:"5px 12px", borderRadius:5, border:"none",
                            background: isLoading ? (darkMode?"rgba(255,255,255,.08)":"#E5E9EF") : C.gold,
                            color: isLoading ? C.textMut : "#fff",
                            fontSize:11, fontWeight:700,
                            cursor: isLoading ? "wait" : "pointer", fontFamily:FONT,
                          }}>
                          {isLoading ? "Fetching…" : "Fetch now"}
                        </button>
                      </div>
                    ) : (
                      <>
                        <div style={{display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:8}}>
                          <div style={{fontSize:9.5, fontWeight:800, color:C.gold, letterSpacing:.6, textTransform:"uppercase"}}>
                            {sum.rows.length} nearby station{sum.rows.length!==1?"s":""}
                          </div>
                          <button
                            onClick={(e)=>{ e.stopPropagation(); fetchStore(sum.store); }}
                            disabled={isLoading}
                            style={{
                              padding:"3px 10px", borderRadius:5,
                              border:`1px solid ${C.cardBord}`, background:"transparent",
                              color:C.gold, fontSize:10, fontWeight:700, cursor: isLoading?"wait":"pointer", fontFamily:FONT,
                            }}>
                            {isLoading ? "Fetching…" : "Refresh this site"}
                          </button>
                        </div>
                        <table style={{width:"100%", borderCollapse:"collapse"}}>
                          <thead>
                            <tr style={{background:darkMode?"rgba(255,255,255,.03)":"#FAFBFD"}}>
                              {["Station","Distance","Source","Regular","Plus","Premium","Diesel","Updated"].map((h,hi)=>(
                                <th key={h} style={{
                                  fontSize:8.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.5,
                                  fontWeight:800, padding:"6px 10px",
                                  textAlign: hi >= 3 && hi <= 6 ? "right" : "left",
                                  borderBottom:`1px solid ${C.cardBord}`, fontFamily:"Arial,sans-serif",
                                }}>{h}</th>
                              ))}
                            </tr>
                          </thead>
                          <tbody>
                            {sum.rows.map((r,ri)=>(
                              <tr key={r.stationId} style={{borderBottom: ri < sum.rows.length-1 ? `1px solid ${C.cardBord}` : "none"}}>
                                <td style={{padding:"6px 10px", fontSize:11, fontWeight:600, color:C.textPri}}>
                                  <a href={r.gbUrl} target="_blank" rel="noopener noreferrer"
                                    style={{color:C.textPri, textDecoration:"none"}}>
                                    {r.brand}
                                  </a>
                                </td>
                                <td style={{padding:"6px 10px", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif"}}>
                                  {r.distanceMi} mi
                                </td>
                                <td style={{padding:"6px 10px"}}>
                                  <span style={{
                                    fontSize:8, fontWeight:800, padding:"1px 5px", borderRadius:3,
                                    background: r.source === "live"
                                      ? (darkMode?"rgba(22,163,74,.15)":"#F0FDF4")
                                      : r.source === "cache"
                                        ? (darkMode?"rgba(8,145,178,.15)":"#ECFEFF")
                                        : (darkMode?"rgba(245,158,11,.15)":"#F8FAFB"),
                                    color: r.source === "live" ? "#16A34A" : r.source === "cache" ? "#0891B2" : "#B45309",
                                    letterSpacing:.4, textTransform:"uppercase",
                                  }}>{r.source}</span>
                                </td>
                                {SALES_GRADES.map(g => {
                                  const ours = sum.store.streetPrice[g];
                                  const theirs = r.prices[g];
                                  const better = theirs < ours;
                                  return (
                                    <td key={g} style={{
                                      padding:"6px 10px", fontSize:11, textAlign:"right",
                                      fontWeight: better ? 800 : 600,
                                      color: better ? "#DC2626" : C.textPri,
                                      fontFamily:"Arial,sans-serif",
                                    }}>
                                      ${theirs?.toFixed(3)}
                                      <div style={{fontSize:8.5, color: better ? "#DC2626" : C.textMut, fontWeight:600, marginTop:1}}>
                                        {(theirs - ours > 0 ? "+" : "")}${(theirs - ours).toFixed(3)}
                                      </div>
                                    </td>
                                  );
                                })}
                                <td style={{padding:"6px 10px", fontSize:9.5, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                                  {new Date(r.fetchedAt).toLocaleTimeString("en-US",{hour:"numeric",minute:"2-digit"})}
                                </td>
                              </tr>
                            ))}
                          </tbody>
                        </table>
                      </>
                    )}
                  </div>
                )}
              </div>
            );
          })}
        </div>
      </div>

      {/* Cost confirmation modal for "Refresh all sites" */}
      {showCostModal && (
        <div onClick={()=>setShowCostModal(false)}
          style={{
            position:"fixed", inset:0, zIndex:9999,
            background:"rgba(8,15,26,.65)", backdropFilter:"blur(3px)",
            display:"flex", alignItems:"center", justifyContent:"center", padding:20,
          }}>
          <div onClick={e=>e.stopPropagation()}
            style={{
              width:"min(520px, 100%)",
              background:C.cardBg, borderRadius:12,
              border:`1px solid ${C.cardBord}`,
              boxShadow:"0 20px 60px rgba(0,0,0,.4)",
              fontFamily:FONT, overflow:"hidden",
            }}>
            <div style={{padding:"14px 18px", background:"#0D1B2A", color:"#fff"}}>
              <div style={{fontSize:11, fontWeight:800, letterSpacing:1.2, textTransform:"uppercase", opacity:.9}}>
                Bulk fetch confirmation
              </div>
              <div style={{fontSize:16, fontWeight:800, marginTop:2}}>
                Refresh competitor prices for all sites
              </div>
            </div>
            <div style={{padding:"16px 18px"}}>
              <div style={{display:"grid", gridTemplateColumns:"repeat(3,1fr)", gap:8, marginBottom:14}}>
                <div style={{padding:"10px 12px", borderRadius:7, border:`1px solid ${C.cardBord}`,
                  background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD"}}>
                  <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase"}}>Sites</div>
                  <div style={{fontSize:18, fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif"}}>{stores.length}</div>
                </div>
                <div style={{padding:"10px 12px", borderRadius:7, border:`1px solid ${C.cardBord}`,
                  background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD"}}>
                  <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase"}}>Need refresh</div>
                  <div style={{fontSize:18, fontWeight:800, color: staleCount === 0 ? "#16A34A" : C.textPri, fontFamily:"Arial,sans-serif"}}>{staleCount}</div>
                </div>
                <div style={{padding:"10px 12px", borderRadius:7, border:`1px solid ${C.cardBord}`,
                  background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD"}}>
                  <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase"}}>Est. credits</div>
                  <div style={{fontSize:18, fontWeight:800, color: estimatedCredits > 5000 ? "#EA580C" : C.textPri, fontFamily:"Arial,sans-serif"}}>
                    ~{estimatedCredits.toLocaleString()}
                  </div>
                </div>
              </div>
              <div style={{
                padding:"10px 12px", borderRadius:7, marginBottom:14,
                background: darkMode?"rgba(8,145,178,.08)":"#ECFEFF",
                border:"1px solid rgba(8,145,178,.3)",
                fontSize:10.5, color: darkMode?"#67E8F9":"#155E75", lineHeight:1.5,
              }}>
                <strong>Smart refresh:</strong> stores with cache &lt; 1 hour old are skipped automatically.
                {staleCount === 0 ? " Everything is fresh — nothing will be fetched unless you Force." : ` Only the ${staleCount} stale store${staleCount!==1?"s":""} will be re-fetched.`}
                {!apiKey && <div style={{marginTop:4, color:darkMode?"#FCD34D":"#92400E"}}>No API key set — fetches will return mock data.</div>}
              </div>
            </div>
            <div style={{
              padding:"12px 18px", borderTop:`1px solid ${C.cardBord}`,
              display:"flex", justifyContent:"flex-end", gap:8,
              background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
            }}>
              <button onClick={()=>setShowCostModal(false)}
                style={{
                  padding:"8px 14px", borderRadius:6,
                  border:`1px solid ${C.cardBord}`, background:"transparent",
                  color:C.textSec, fontSize:11, fontWeight:600, cursor:"pointer", fontFamily:FONT,
                }}>
                Cancel
              </button>
              <button onClick={()=>handleRefreshAll(true)}
                style={{
                  padding:"8px 14px", borderRadius:6,
                  border:"1px solid rgba(234,88,12,.4)", background:"transparent",
                  color:"#EA580C", fontSize:11, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                }}>
                Force refresh all
              </button>
              <button onClick={()=>handleRefreshAll(false)}
                disabled={staleCount === 0}
                style={{
                  padding:"8px 14px", borderRadius:6, border:"none",
                  background: staleCount === 0 ? (darkMode?"rgba(255,255,255,.08)":"#E5E9EF") : "#0D1B2A",
                  color: staleCount === 0 ? C.textMut : "#fff",
                  fontSize:11, fontWeight:800,
                  cursor: staleCount === 0 ? "not-allowed" : "pointer", fontFamily:FONT,
                }}>
                {staleCount === 0 ? "Nothing to refresh" : `Fetch ${staleCount} stale site${staleCount!==1?"s":""}`}
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}


// Historical rack price data (30 days) — grounded in real EIA weekly retail
// price data for PADD 1C (Lower Atlantic). Source: EIA Weekly Retail
// Gasoline Prices, series EMM_EPMR_PTE_R1Z_DPG.
//
// Weekly anchors are real EIA published retail prices:
//   - 2026-03-23: $3.785  (EIA published, baseline for 30-day window)
//   - 2026-03-30: $3.88   (projected from EIA national trend)
//   - 2026-04-06: $3.95   (national $4.12, PADD 1C ~$0.17 lower)
//   - 2026-04-13: $3.99   (national peak week, modest pullback)
//   - 2026-04-20: $3.93   (national down 3.5¢, PADD 1C tracking)
//
// Retail-to-rack conversion removes ~$0.78/gal in taxes and margins:
//   - Federal excise: $0.184 gasoline, $0.244 diesel
//   - SE state tax average: ~$0.33
//   - Retail margin: ~$0.18
//   - Terminal-to-pump freight: ~$0.05
//
// Diesel and Premium series are derived from the Regular trajectory with
// grade-specific spreads: Premium runs ~$0.25 over Regular; Diesel shows
// more volatile trajectory in 2026 due to distillate tightness.
//
// Each terminal's 30-day history is anchored such that day 30 equals its
// current rack price (from RACK_PRICES), with the prior 30 days tracking
// the shape of the real EIA retail curve.
function genRackHistory() {
  // Weekly EIA retail anchors for PADD 1C Regular (real data):
  const weeklyRetail = [3.785, 3.880, 3.950, 3.990, 3.930];
  // Day indices of each anchor within the 30-day window (0 = 30 days ago):
  const anchorDays = [0, 7, 14, 21, 28];
  // Build a 31-point retail curve by linear interpolation between anchors
  const dailyRetailRegular = [];
  for (let d = 0; d <= 30; d++) {
    // Find surrounding anchors
    let lo = 0, hi = 0;
    for (let i = 0; i < anchorDays.length - 1; i++) {
      if (d >= anchorDays[i] && d <= anchorDays[i+1]) { lo = i; hi = i+1; break; }
      if (d >= anchorDays[anchorDays.length-1]) { lo = hi = anchorDays.length-1; }
    }
    const t = anchorDays[hi] === anchorDays[lo] ? 0 : (d - anchorDays[lo]) / (anchorDays[hi] - anchorDays[lo]);
    const retail = weeklyRetail[lo] + (weeklyRetail[hi] - weeklyRetail[lo]) * t;
    // Add small deterministic daily noise (±$0.008/gal) using a seeded jitter
    const noise = (Math.sin(d * 2.37) * 0.008);
    dailyRetailRegular.push(retail + noise);
  }
  // Premium follows Regular + $0.25 consistent spread
  const dailyRetailPremium = dailyRetailRegular.map(v => v + 0.25);
  // Diesel had a steeper rise from Hormuz — build its own shape with anchor
  // retail values that reflect the real distillate curve (higher peak, wider swing)
  const weeklyRetailDiesel = [5.395, 5.520, 5.640, 5.700, 5.610];
  const dailyRetailDiesel = [];
  for (let d = 0; d <= 30; d++) {
    let lo = 0, hi = 0;
    for (let i = 0; i < anchorDays.length - 1; i++) {
      if (d >= anchorDays[i] && d <= anchorDays[i+1]) { lo = i; hi = i+1; break; }
      if (d >= anchorDays[anchorDays.length-1]) { lo = hi = anchorDays.length-1; }
    }
    const t = anchorDays[hi] === anchorDays[lo] ? 0 : (d - anchorDays[lo]) / (anchorDays[hi] - anchorDays[lo]);
    const retail = weeklyRetailDiesel[lo] + (weeklyRetailDiesel[hi] - weeklyRetailDiesel[lo]) * t;
    const noise = (Math.cos(d * 1.91) * 0.010);
    dailyRetailDiesel.push(retail + noise);
  }
  const dailyRetail = { Regular: dailyRetailRegular, Premium: dailyRetailPremium, Diesel: dailyRetailDiesel };

  const hist = {};
  TERMINALS.forEach(t => {
    hist[t.id] = {};
    GRADES.forEach(g => {
      const currentRack = RACK_PRICES[t.id][g];
      const retailToday = dailyRetail[g][30];
      // Offset: difference between current rack and today's retail — carries
      // tax/margin/freight backout plus terminal-specific basis
      const offset = currentRack - retailToday;
      // Build series: each day's rack = retail_curve[day] + offset, rounded to 4dp
      const arr = dailyRetail[g].map(v => +(v + offset).toFixed(4));
      hist[t.id][g] = arr;
    });
  });
  return hist;
}
const RACK_HISTORY = genRackHistory();

// NYMEX data (30 days)
function genNYMEX() {
  const ulsd = [], rbob = [], crude = [];
  // Starting values calibrated to April 2026 spot market:
  // ULSD elevated due to distillate tightness (Hormuz-era supply concerns),
  // RBOB reflects seasonal pre-summer driving demand, WTI crude $95-100 range.
  let u = 4.18, r = 2.62, c = 96.5;
  for (let i = 0; i < 31; i++) {
    u += (Math.random() - 0.48) * 0.05;
    r += (Math.random() - 0.48) * 0.04;
    c += (Math.random() - 0.48) * 1.2;
    ulsd.push(+u.toFixed(4));
    rbob.push(+r.toFixed(4));
    crude.push(+c.toFixed(2));
  }
  return { ulsd, rbob, crude };
}
const NYMEX = genNYMEX();

// ─── NYMEX FORWARD CURVE — 12 months of futures prices ──────────────────────
// The futures strip a procurement manager sees on their screen every morning.
// Each entry is one contract month. Real deployments pull this from CME via
// a feed like Refinitiv or Bloomberg; the demo uses a seeded generator that
// produces a realistic curve shape. Shape patterns to recognize:
//   - Contango (upward slope): normal carrying-cost market, lift now
//   - Backwardation (downward slope): tight supply now, defer if possible
//   - Seasonal humps: summer RBOB peaks, winter HO peaks
// Values are in $/gal.
function genForwardCurve() {
  const now = new Date();
  const startMonth = now.getMonth(); // 0-11
  const months = [];
  const rbob = [], ulsd = [];
  // Near-month anchors from NYMEX spot
  let rbobPrice = NYMEX.rbob[NYMEX.rbob.length-1] || 2.62;
  let ulsdPrice = NYMEX.ulsd[NYMEX.ulsd.length-1] || 4.18;
  const MONTH_NAMES = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"];
  for (let i = 0; i < 12; i++) {
    const m = (startMonth + i) % 12;
    const y = now.getFullYear() + Math.floor((startMonth + i) / 12);
    months.push(`${MONTH_NAMES[m]} ${String(y).slice(2)}`);
    // RBOB has a summer peak (May-Aug higher), slight contango overall (+$0.003/mo base)
    const summerBump = [0, 0, 0.003, 0.008, 0.014, 0.018, 0.016, 0.010, 0.004, 0, 0, 0][m];
    rbobPrice = rbobPrice + 0.003 + summerBump + (Math.random() - 0.5) * 0.008;
    rbob.push(+rbobPrice.toFixed(4));
    // ULSD has a winter peak (Dec-Feb higher), mild contango
    const winterBump = [0.012, 0.010, 0.004, 0, 0, 0, 0, 0, 0, 0.003, 0.008, 0.014][m];
    ulsdPrice = ulsdPrice + 0.002 + winterBump + (Math.random() - 0.5) * 0.006;
    ulsd.push(+ulsdPrice.toFixed(4));
  }
  return { months, rbob, ulsd };
}
const FORWARD_CURVE = genForwardCurve();

// Compute the curve slope over the first N months — the procurement manager's
// core signal. Positive = contango (rising), negative = backwardation (falling).
// Returns slope in $/gal/month and a total spread over the window.
function curveSlope(prices, windowMonths = 3) {
  if (!prices || prices.length < 2) return { perMonth: 0, spread: 0, shape: "flat" };
  const start = prices[0];
  const end = prices[Math.min(windowMonths, prices.length-1)];
  const spread = end - start;
  const perMonth = spread / windowMonths;
  const shape = perMonth > 0.005 ? "contango"
              : perMonth < -0.005 ? "backwardation"
              : "flat";
  return { perMonth, spread, shape };
}


//  FORECAST ENGINE 
// Simulated 14-day forward price forecast (AR(2) on NYMEX, translated to rack)
function genForward() {
  const days = 14;
  const result = {};
  TERMINALS.forEach(t => {
    result[t.id] = {};
    GRADES.forEach(g => {
      const base = RACK_PRICES[t.id][g];
      const pts = [];
      let v = base, drift = (Math.random()-0.46)*0.008;
      for (let i=0; i<days; i++) {
        drift = drift*0.85 + (Math.random()-0.48)*0.004;
        v = Math.max(base*0.92, v + drift);
        const ci = 0.012 + i*0.0025;
        pts.push({ day:i+1, val:+v.toFixed(4), lo:+(v-ci).toFixed(4), hi:+(v+ci).toFixed(4) });
      }
      result[t.id][g] = pts;
    });
  });
  return result;
}
const FORWARD = genForward();

//  PROCUREMENT SIGNALS 
// Signal logic: based on 3-day rack trend + pipeline window + inventory risk
function genSignals() {
  const out = {};
  TERMINALS.forEach(t => {
    out[t.id] = {};
    GRADES.forEach(g => {
      const hist = RACK_HISTORY[t.id][g];
      const n = hist.length;
      const t3 = hist[n-1] - hist[n-4];  // 3-day change
      const t7 = hist[n-1] - hist[n-8];  // 7-day change
      const fwd3 = FORWARD[t.id][g][2];   // forecast day 3
      const rising = fwd3.val > hist[n-1] + 0.004;
      const win = COLONIAL.terminalWindows[t.id];
      const windowOpen = win?.daysToWindow === 0;
      let signal, color, reason, savingsNote, urgency;
      if (t3 > 0.014 && rising) {
        signal="BUY NOW"; color="#22C55E"; urgency=3;
        reason=`Rack up $${t3.toFixed(4)} in 3 days, forecast +$${(fwd3.val-hist[n-1]).toFixed(4)} more`;
        savingsNote=`Buying today saves ~$${(t3*0.5*50000).toFixed(0)} vs waiting on 50K gal`;
      } else if (t3 < -0.010) {
        signal="WAIT"; color="#F59E0B"; urgency=1;
        reason=`Rack falling — down $${Math.abs(t3).toFixed(4)} in 3 days, forecast continues lower`;
        savingsNote=`Waiting 3 days may save ~$${(Math.abs(t3)*0.6*50000).toFixed(0)} on 50K gal`;
      } else if (!windowOpen && win?.daysToWindow<=1) {
        signal="SCHEDULE"; color="#3B82F6"; urgency=2;
        reason=`Pipeline window opens in ${win?.daysToWindow===0?"<1":win?.daysToWindow} day${win?.daysToWindow!==1?"s":""}`;
        savingsNote="Nominate now — window closes soon";
      } else {
        signal="ON PLAN"; color="#7B8FAF"; urgency=0;
        reason="Price stable, no urgency — execute per schedule";
        savingsNote="No arbitrage opportunity detected";
      }
      out[t.id][g] = { signal, color, reason, savingsNote, urgency, trend3d:t3, trend7d:t7 };
    });
  });
  return out;
}
const SIGNALS = genSignals();

//  DEPLETION FORECAST 
// For each store × grade, project days until reorder trigger and critical low.
// Aligned with s.daysSupply — uses the same effectiveDailyVol (includes Plus
// blend draw) and no random noise, so Store Map numbers match Inventory.
const DEPLETION = STORES.map(s => {
  const forecast = {};
  GRADES.forEach(g => {
    const inv = s.invLevel[g];
    const dailyDraw = s.effectiveDailyVol[g]; // matches s.daysSupply formula
    const daysToReorder = inv / dailyDraw;                        // = s.daysSupply[g]
    const daysToCritical = (inv - s.tanks[g] * 0.12) / dailyDraw;  // days until tank hits 12% buffer
    forecast[g] = {
      daysToReorder: +daysToReorder.toFixed(1),
      daysToCritical: +daysToCritical.toFixed(1),
      projectedEmpty: +daysToReorder.toFixed(1),
      dailyDraw: +dailyDraw.toFixed(0),
    };
  });
  const minCritical = Math.min(...GRADES.map(g=>forecast[g].daysToCritical));
  const minReorder  = Math.min(...GRADES.map(g=>forecast[g].daysToReorder));
  return { storeId:s.id, storeName:s.name, state:s.state, terminal:s.terminal, forecast, minCritical, minReorder };
});

//  EXPOSURE DATA 
const MONTHLY_VOL = STORES.reduce((a,s)=>a+s.totalDailyVol*30,0);
const HEDGED_VOL  = Math.round(MONTHLY_VOL * 0.38); // simulate 38% hedged
const UNHEDGED    = MONTHLY_VOL - HEDGED_VOL;
const AVG_LANDED  = STORES.reduce((a,s)=>a+s.blendedMargin+3.40,0)/STORES.length; // rough blended cost (updated for current 2026 rack levels)

// Action items derived from signals
function genActionQueue() {
  const actions = [];
  // High-urgency signal actions
  TERMINALS.forEach(t => {
    GRADES.forEach(g => {
      const sig = SIGNALS[t.id][g];
      if (sig.urgency >= 2) {
        const stores = STORES.filter(s=>s.terminal===t.id);
        const vol = stores.reduce((a,s)=>a+s.dailyVol[g]*3,0); // 3-day supply
        actions.push({
          id:`sig-${t.id}-${g}`, type:"signal", urgency:sig.urgency,
          title:`${sig.signal}: ${g} at ${t.short}`,
          desc:sig.reason,
          savings:sig.savingsNote,
          volume:vol,
          deadline:COLONIAL.terminalWindows[t.id]?.daysToWindow===0?"Window open now":"Nominate today",
          color:sig.color,
          terminal:t.id,
        });
      }
    });
  });
  // Critical inventory actions
  DEPLETION.filter(d=>d.minCritical<=1).forEach(d => {
    actions.push({
      id:`inv-${d.storeId}`, type:"inventory", urgency:4,
      title:`CRITICAL: ${d.storeName}`,
      desc:`Inventory hits critical in <1 day — emergency order required`,
      savings:"Stockout costs $8–15K per incident in lost sales",
      volume:STORES.find(s=>s.id===d.storeId)?.totalDailyVol||0,
      deadline:"Order now — same-day delivery required",
      color:"#EF4444",
      terminal:STORES.find(s=>s.id===d.storeId)?.terminal,
    });
  });
  // Nomination deadline
  actions.push({
    id:"nom-deadline", type:"deadline", urgency:3,
    title:"Colonial Nomination Deadline Tomorrow",
    desc:`Nominations for Apr 16 lifts due ${COLONIAL.nominationDeadline}`,
    savings:"Missing deadline means waiting 10 days for next cycle",
    volume:0,
    deadline:COLONIAL.nominationDeadline,
    color:"#F59E0B",
    terminal:null,
  });
  return actions.sort((a,b)=>b.urgency-a.urgency).slice(0,8);
}
const ACTION_QUEUE = genActionQueue();

//  CARRIER DATA 
//  CARRIER DATA 
const CARRIER_FLEET = [
  {
    id:"c1", name:"Southeast Fuel Transport", short:"SFT",
    dot:"2847391", mc:"MC-449821", scac:"SEFT",
    trucks:8, available:5,
    tractors:[
      {id:"SFT-01",unit:"T-101",driver:"Marcus Webb",  hos:8.5,  status:"LOADING",   location:"Selma Terminal",        eta:"09:45",odometer:284750,lastInspect:"Apr 17"},
      {id:"SFT-02",unit:"T-102",driver:"James Pruitt", hos:11.0, status:"EN ROUTE",  location:"I-40 E mm 214",         eta:"11:20",odometer:312180,lastInspect:"Apr 02"},
      {id:"SFT-03",unit:"T-103",driver:"Deon Harris",  hos:6.2,  status:"DELIVERING",location:"Cary Crossroads Fuel",  eta:"10:15",odometer:198430,lastInspect:"Apr 08"},
      {id:"SFT-04",unit:"T-104",driver:"Ray Simmons",  hos:14.0, status:"AVAILABLE", location:"Charlotte terminal",     eta:null,   odometer:441220,lastInspect:"Mar 17"},
      {id:"SFT-05",unit:"T-105",driver:"Kevin Lloyd",  hos:9.5,  status:"AVAILABLE", location:"Selma yard",            eta:null,   odometer:267890,lastInspect:"Apr 16"},
      {id:"SFT-06",unit:"T-106",driver:"Chris Atkins", hos:4.0,  status:"HOS RESET", location:"Rest area I-85",        eta:null,   odometer:523410,lastInspect:"Mar 24"},
      {id:"SFT-07",unit:"T-107",driver:"Tony Reeves",  hos:10.5, status:"AVAILABLE", location:"Raleigh yard",          eta:null,   odometer:389760,lastInspect:"Apr 05"},
      {id:"SFT-08",unit:"T-108",driver:"Sam Grant",    hos:7.0,  status:"MAINTENANCE",location:"SFT shop — brake job",  eta:null,   odometer:601230,lastInspect:"Feb 14"},
    ],
    compartments:[8000,5000,3000], totalCap:16000,
    rateBase:0.0465, ratePerMile:2.10, detentionRate:85, // $/hr detention
    contract:"Annual", contractExpiry:"Dec 31 2025", minLoads:40, // per month
    hazmatCert:true, vaporRecovery:true, bottomLoad:true, topLoad:true,
    insurance:"$5M liability · $1M cargo", insuranceExpiry:"Jan 1 2026",
    terminalAccess:["selma","charlotte","richmond","atlanta"],
    avgTransitHrs:{ selma:2.1, charlotte:1.8, richmond:3.4, atlanta:2.9 },
    ytdLoads:187, ytdGallons:2840000, ytdDetentionHrs:14.5, ytdOverShort:-42,
    status:"ACTIVE", rating:4.7,
  },
  {
    id:"c2", name:"Carolina Fuel LLC", short:"CFL",
    dot:"1938472", mc:"MC-512034", scac:"CAFL",
    trucks:6, available:4,
    tractors:[
      {id:"CFL-01",unit:"C-201",driver:"Brian Stokes", hos:10.0, status:"AVAILABLE", location:"Charlotte yard",         eta:null,   odometer:156780,lastInspect:"Apr 17"},
      {id:"CFL-02",unit:"C-202",driver:"Aaron Tate",   hos:8.0,  status:"EN ROUTE",  location:"I-77 S mm 48",          eta:"10:50",odometer:234560,lastInspect:"Apr 01"},
      {id:"CFL-03",unit:"C-203",driver:"Reggie Burns", hos:13.5, status:"AVAILABLE", location:"Greensboro yard",       eta:null,   odometer:312900,lastInspect:"Apr 17"},
      {id:"CFL-04",unit:"C-204",driver:"Nate Fowler",  hos:11.5, status:"AVAILABLE", location:"Charlotte yard",        eta:null,   odometer:189340,lastInspect:"Apr 07"},
      {id:"CFL-05",unit:"C-205",driver:"Will Cobb",    hos:9.0,  status:"LOADING",   location:"Charlotte terminal",   eta:"11:00",odometer:276540,lastInspect:"Apr 16"},
      {id:"CFL-06",unit:"C-206",driver:"Dale Penn",    hos:6.5,  status:"HOS RESET", location:"Driver home — Concord", eta:null,   odometer:445230,lastInspect:"Mar 24"},
    ],
    compartments:[10000,8000], totalCap:18000,
    rateBase:0.0420, ratePerMile:2.00, detentionRate:75,
    contract:"Annual", contractExpiry:"Sep 30 2025", minLoads:30,
    hazmatCert:true, vaporRecovery:true, bottomLoad:true, topLoad:false,
    insurance:"$5M liability · $1M cargo", insuranceExpiry:"Jun 1 2025",
    terminalAccess:["charlotte","selma"],
    avgTransitHrs:{ charlotte:1.6, selma:2.3 },
    ytdLoads:141, ytdGallons:2340000, ytdDetentionHrs:8.0, ytdOverShort:+18,
    status:"ACTIVE", rating:4.5,
  },
  {
    id:"c3", name:"Palmetto Petroleum Transport", short:"PPT",
    dot:"3012847", mc:"MC-678234", scac:"PLPT",
    trucks:5, available:3,
    tractors:[
      {id:"PPT-01",unit:"P-301",driver:"Lou Graves",   hos:12.0, status:"AVAILABLE", location:"Columbia SC yard",      eta:null,   odometer:223410,lastInspect:"Apr 09"},
      {id:"PPT-02",unit:"P-302",driver:"Tim Bauer",    hos:9.5,  status:"DELIVERING",location:"Rock Hill Crossroads",  eta:"09:50",odometer:345670,lastInspect:"Apr 03"},
      {id:"PPT-03",unit:"P-303",driver:"Jake Sims",    hos:11.0, status:"AVAILABLE", location:"Columbia SC yard",      eta:null,   odometer:178920,lastInspect:"Apr 16"},
      {id:"PPT-04",unit:"P-304",driver:"Matt Ingram",  hos:7.5,  status:"EN ROUTE",  location:"I-26 W mm 101",        eta:"12:30",odometer:412340,lastInspect:"Apr 16"},
      {id:"PPT-05",unit:"P-305",driver:"Ed Cannon",    hos:5.0,  status:"MAINTENANCE",location:"PPT shop — def system", eta:null,   odometer:534820,lastInspect:"Feb 28"},
    ],
    compartments:[7000,5000,4000], totalCap:16000,
    rateBase:0.0515, ratePerMile:2.30, detentionRate:90,
    contract:"Spot + preferred", contractExpiry:"Rolling", minLoads:15,
    hazmatCert:true, vaporRecovery:true, bottomLoad:true, topLoad:true,
    insurance:"$5M liability · $750K cargo", insuranceExpiry:"Mar 1 2026",
    terminalAccess:["charlotte","jacksonville"],
    avgTransitHrs:{ charlotte:2.4, jacksonville:3.1 },
    ytdLoads:98, ytdGallons:1480000, ytdDetentionHrs:21.0, ytdOverShort:-87,
    status:"ACTIVE", rating:4.2,
  },
  {
    id:"c4", name:"Blue Ridge Delivery", short:"BRD",
    dot:"2193847", mc:"MC-334512", scac:"BRDY",
    trucks:6, available:2,
    tractors:[
      {id:"BRD-01",unit:"B-401",driver:"Carl Potts",   hos:10.5, status:"LOADING",   location:"Richmond terminal",    eta:"10:30",odometer:298340,lastInspect:"Apr 04"},
      {id:"BRD-02",unit:"B-402",driver:"Glenn Hood",   hos:8.5,  status:"EN ROUTE",  location:"I-95 S mm 88",        eta:"11:45",odometer:367210,lastInspect:"Apr 16"},
      {id:"BRD-03",unit:"B-403",driver:"Frank Wills",  hos:13.5, status:"AVAILABLE", location:"Richmond yard",        eta:null,   odometer:142780,lastInspect:"Apr 17"},
      {id:"BRD-04",unit:"B-404",driver:"Don Kidd",     hos:11.0, status:"AVAILABLE", location:"Fredericksburg yard",  eta:null,   odometer:489230,lastInspect:"Mar 24"},
      {id:"BRD-05",unit:"B-405",driver:"Steve Pratt",  hos:6.0,  status:"HOS RESET", location:"Rest area I-81",       eta:null,   odometer:623410,lastInspect:"Feb 19"},
      {id:"BRD-06",unit:"B-406",driver:"Paul Nolen",   hos:9.0,  status:"MAINTENANCE",location:"BRD shop — tire replacement",eta:null,odometer:387650,lastInspect:"Mar 08"},
    ],
    compartments:[9000,7000,5000], totalCap:21000,
    rateBase:0.0490, ratePerMile:2.20, detentionRate:80,
    contract:"Annual", contractExpiry:"Jun 30 2025", minLoads:25,
    hazmatCert:true, vaporRecovery:false, bottomLoad:true, topLoad:true,
    insurance:"$5M liability · $1M cargo", insuranceExpiry:"Jul 1 2025",
    terminalAccess:["richmond","selma"],
    avgTransitHrs:{ richmond:1.9, selma:3.8 },
    ytdLoads:119, ytdGallons:2150000, ytdDetentionHrs:31.5, ytdOverShort:+64,
    status:"ACTIVE", rating:4.0,
    alerts:["Insurance renews Jun 30 — need COI update","No vapor recovery — cannot serve CARB stores"],
  },
  {
    id:"c5", name:"Coastal Carriers Inc.", short:"CCI",
    dot:"3284710", mc:"MC-782341", scac:"CCIC",
    trucks:8, available:6,
    tractors:[
      {id:"CCI-01",unit:"CC-501",driver:"Roy Marsh",   hos:11.5, status:"AVAILABLE", location:"Jacksonville yard",    eta:null,   odometer:203480,lastInspect:"Apr 16"},
      {id:"CCI-02",unit:"CC-502",driver:"Cal Dixon",   hos:10.0, status:"AVAILABLE", location:"Tampa yard",           eta:null,   odometer:178920,lastInspect:"Apr 08"},
      {id:"CCI-03",unit:"CC-503",driver:"Bart King",   hos:9.0,  status:"DELIVERING",location:"Orlando Theme Park",   eta:"10:00",odometer:312670,lastInspect:"Apr 05"},
      {id:"CCI-04",unit:"CC-504",driver:"Wade Eaton",  hos:8.5,  status:"EN ROUTE",  location:"I-75 N mm 312",       eta:"13:00",odometer:267340,lastInspect:"Apr 03"},
      {id:"CCI-05",unit:"CC-505",driver:"Clint Moody", hos:12.5, status:"AVAILABLE", location:"Jacksonville yard",    eta:null,   odometer:134560,lastInspect:"Apr 16"},
      {id:"CCI-06",unit:"CC-506",driver:"Dean Webb",   hos:10.5, status:"AVAILABLE", location:"Miami yard",           eta:null,   odometer:289430,lastInspect:"Apr 01"},
      {id:"CCI-07",unit:"CC-507",driver:"Jim Holt",    hos:7.0,  status:"AVAILABLE", location:"Tampa yard",           eta:null,   odometer:456780,lastInspect:"Mar 24"},
      {id:"CCI-08",unit:"CC-508",driver:"Ned Phelps",  hos:13.0, status:"LOADING",   location:"Tampa terminal",      eta:"11:30",odometer:345210,lastInspect:"Apr 17"},
    ],
    compartments:[8000,6000,2000], totalCap:16000,
    rateBase:0.0445, ratePerMile:2.05, detentionRate:70,
    contract:"Annual", contractExpiry:"Dec 31 2025", minLoads:50,
    hazmatCert:true, vaporRecovery:true, bottomLoad:true, topLoad:true,
    insurance:"$10M liability · $2M cargo", insuranceExpiry:"Feb 1 2026",
    terminalAccess:["jacksonville","tampa"],
    avgTransitHrs:{ jacksonville:2.0, tampa:1.7 },
    ytdLoads:231, ytdGallons:3480000, ytdDetentionHrs:9.5, ytdOverShort:-12,
    status:"ACTIVE", rating:4.8,
  },
  {
    id:"c6", name:"Atlantic Fuel Services", short:"AFS",
    dot:"1847293", mc:"MC-221983", scac:"ATFS",
    trucks:4, available:3,
    tractors:[
      {id:"AFS-01",unit:"A-601",driver:"Hank Gilmore", hos:12.0, status:"AVAILABLE", location:"Atlanta yard",         eta:null,   odometer:234780,lastInspect:"Apr 09"},
      {id:"AFS-02",unit:"A-602",driver:"Bud Thornton", hos:9.5,  status:"EN ROUTE",  location:"I-20 E mm 56",        eta:"11:15",odometer:389120,lastInspect:"Apr 16"},
      {id:"AFS-03",unit:"A-603",driver:"Vince Pryor",  hos:11.0, status:"AVAILABLE", location:"Atlanta yard",         eta:null,   odometer:167340,lastInspect:"Apr 17"},
      {id:"AFS-04",unit:"A-604",driver:"Stan Boone",   hos:8.0,  status:"AVAILABLE", location:"Savannah yard",        eta:null,   odometer:298430,lastInspect:"Apr 06"},
    ],
    compartments:[12000,8000], totalCap:20000,
    rateBase:0.0395, ratePerMile:1.95, detentionRate:65,
    contract:"Annual", contractExpiry:"Apr 2 2026", minLoads:35,
    hazmatCert:true, vaporRecovery:true, bottomLoad:true, topLoad:true,
    insurance:"$5M liability · $1M cargo", insuranceExpiry:"Apr 1 2026",
    terminalAccess:["atlanta","jacksonville"],
    avgTransitHrs:{ atlanta:2.2, jacksonville:2.8 },
    ytdLoads:163, ytdGallons:2920000, ytdDetentionHrs:6.0, ytdOverShort:+33,
    status:"ACTIVE", rating:4.6,
  },
];

// Simulated active loads in transit / at terminal
const ACTIVE_LOADS = [
  { id:"LD-4401", carrier:"SFT", truck:"T-102", driver:"James Pruitt",  origin:"Selma, NC",     dest:"I-40 Travel Center",    grade:"Diesel",  gals:14000, status:"EN ROUTE",   pct:62, bol:"SEL-20250414-0892", tempF:67, apiGravity:34.2, bsmtTicket:"0892-A", eta:"11:20", departed:"07:30", detained:0   },
  { id:"LD-4402", carrier:"SFT", truck:"T-103", driver:"Deon Harris",   origin:"Selma, NC",     dest:"Cary Crossroads Fuel",  grade:"Regular", gals:8000,  status:"DELIVERING",  pct:95, bol:"SEL-20250414-0893", tempF:65, apiGravity:58.1, bsmtTicket:"0893-A", eta:"10:15", departed:"08:00", detained:0   },
  { id:"LD-4403", carrier:"CFL", truck:"C-202", driver:"Aaron Tate",    origin:"Charlotte, NC", dest:"Greensboro Gateway",    grade:"Regular", gals:18000, status:"EN ROUTE",   pct:38, bol:"CLT-20250414-0441", tempF:66, apiGravity:57.8, bsmtTicket:"0441-B", eta:"10:50", departed:"09:10", detained:0   },
  { id:"LD-4404", carrier:"PPT", truck:"P-302", driver:"Tim Bauer",     origin:"Charlotte, NC", dest:"Rock Hill Crossroads",  grade:"Diesel",  gals:12000, status:"DELIVERING",  pct:90, bol:"CLT-20250414-0442", tempF:68, apiGravity:33.9, bsmtTicket:"0442-C", eta:"09:50", departed:"07:45", detained:22  },
  { id:"LD-4405", carrier:"BRD", truck:"B-401", driver:"Carl Potts",    origin:"Richmond, VA",  dest:"Richmond Boulevard",    grade:"Premium", gals:16000, status:"LOADING",     pct:8,  bol:"RIC-20250414-0211", tempF:null, apiGravity:null, bsmtTicket:null, eta:"10:30", departed:null, detained:0   },
  { id:"LD-4406", carrier:"BRD", truck:"B-402", driver:"Glenn Hood",    origin:"Richmond, VA",  dest:"Alexandria Beltway",    grade:"Regular", gals:21000, status:"EN ROUTE",   pct:51, bol:"RIC-20250414-0212", tempF:65, apiGravity:57.2, bsmtTicket:"0212-A", eta:"11:45", departed:"08:30", detained:0   },
  { id:"LD-4407", carrier:"CCI", truck:"CC-503",driver:"Bart King",     origin:"Tampa, FL",     dest:"Orlando Theme Park",    grade:"Regular", gals:16000, status:"DELIVERING",  pct:88, bol:"TPA-20250414-0654", tempF:72, apiGravity:57.5, bsmtTicket:"0654-A", eta:"10:00", departed:"07:15", detained:45  },
  { id:"LD-4408", carrier:"CCI", truck:"CC-504",driver:"Wade Eaton",    origin:"Jacksonville,FL",dest:"Daytona Beach",        grade:"Diesel",  gals:16000, status:"EN ROUTE",   pct:28, bol:"JAX-20250414-0327", tempF:70, apiGravity:34.1, bsmtTicket:"0327-B", eta:"13:00", departed:"09:45", detained:0   },
  { id:"LD-4409", carrier:"CCI", truck:"CC-508",driver:"Ned Phelps",    origin:"Tampa, FL",     dest:"Clearwater Beach",      grade:"Premium", gals:14000, status:"LOADING",     pct:15, bol:"TPA-20250414-0655", tempF:null, apiGravity:null, bsmtTicket:null, eta:"11:30", departed:null, detained:0   },
  { id:"LD-4410", carrier:"SFT", truck:"T-101", driver:"Marcus Webb",   origin:"Selma, NC",     dest:"Raleigh North Express", grade:"Regular", gals:16000, status:"LOADING",     pct:5,  bol:"SEL-20250414-0894", tempF:null, apiGravity:null, bsmtTicket:null, eta:"09:45", departed:null, detained:15  },
  { id:"LD-4411", carrier:"AFS", truck:"A-602", driver:"Bud Thornton",  origin:"Doraville, GA", dest:"Atlanta Perimeter",     grade:"Regular", gals:20000, status:"EN ROUTE",   pct:44, bol:"ATL-20250414-0118", tempF:68, apiGravity:57.9, bsmtTicket:"0118-A", eta:"11:15", departed:"08:50", detained:0   },
  { id:"LD-4412", carrier:"PPT", truck:"P-304", driver:"Matt Ingram",   origin:"Charlotte, NC", dest:"Spartanburg I-85",      grade:"Diesel",  gals:16000, status:"EN ROUTE",   pct:19, bol:"CLT-20250414-0443", tempF:67, apiGravity:34.0, bsmtTicket:"0443-A", eta:"12:30", departed:"09:55", detained:0   },
];

// Terminal congestion / rack wait times (simulated real-time)
const TERMINAL_STATUS = {
  selma:       { rackWait:22, lanesOpen:4, lanesTotal:6, congestion:"MODERATE", lastLoad:"09:12", nextAvail:"09:30" },
  apex:        { rackWait:12, lanesOpen:4, lanesTotal:4, congestion:"LOW",      lastLoad:"09:22", nextAvail:"09:35" },
  charlotte:   { rackWait:8,  lanesOpen:6, lanesTotal:6, congestion:"LOW",      lastLoad:"09:18", nextAvail:"09:25" },
  richmond:    { rackWait:45, lanesOpen:3, lanesTotal:5, congestion:"HIGH",     lastLoad:"09:05", nextAvail:"09:50" },
  atlanta:     { rackWait:15, lanesOpen:5, lanesTotal:6, congestion:"LOW",      lastLoad:"09:20", nextAvail:"09:35" },
  macon:       { rackWait:20, lanesOpen:3, lanesTotal:4, congestion:"MODERATE", lastLoad:"09:10", nextAvail:"09:32" },
  bainbridge:  { rackWait:10, lanesOpen:2, lanesTotal:3, congestion:"LOW",      lastLoad:"09:25", nextAvail:"09:38" },
  birmingham:  { rackWait:25, lanesOpen:5, lanesTotal:7, congestion:"MODERATE", lastLoad:"09:14", nextAvail:"09:42" },
  jacksonville:{ rackWait:30, lanesOpen:4, lanesTotal:5, congestion:"MODERATE", lastLoad:"09:08", nextAvail:"09:40" },
  tampa:       { rackWait:18, lanesOpen:5, lanesTotal:6, congestion:"LOW",      lastLoad:"09:15", nextAvail:"09:33" },
};


// ─── SE US MAP GEOGRAPHY ──────────────────────────────────────────────────────
// Simplified state polygon coordinates [lng, lat] for Southeast US
const SE_GEO = {
  VA:[[-83.68,36.60],[-80.88,36.56],[-77.34,35.97],[-75.88,36.55],[-75.63,37.95],[-76.24,36.98],[-76.30,37.21],[-76.06,37.89],[-76.51,38.53],[-77.04,38.99],[-77.46,39.33],[-77.84,39.13],[-79.65,39.72],[-80.52,39.72],[-81.02,37.45],[-81.75,37.27],[-83.54,37.99],[-83.68,36.60]],
  NC:[[-84.32,35.00],[-80.88,36.56],[-77.34,35.97],[-75.88,36.55],[-75.47,35.25],[-76.13,34.72],[-77.22,34.17],[-77.95,33.85],[-78.56,33.88],[-79.10,34.30],[-80.08,34.88],[-80.93,35.10],[-84.32,35.00]],
  SC:[[-83.35,32.08],[-82.59,33.59],[-81.42,33.96],[-80.93,35.10],[-80.08,34.88],[-79.10,34.30],[-78.56,33.88],[-79.45,34.31],[-80.80,32.05],[-81.12,32.12],[-81.75,32.16],[-83.35,32.08]],
  GA:[[-85.60,34.98],[-84.32,35.00],[-80.93,35.10],[-81.42,33.96],[-82.59,33.59],[-83.35,32.08],[-81.75,32.16],[-81.44,31.72],[-81.18,31.20],[-81.00,30.99],[-84.88,30.75],[-84.87,31.00],[-85.00,31.00],[-85.00,32.00],[-85.60,34.98]],
  FL:[[-87.63,30.87],[-85.00,31.00],[-84.88,30.75],[-81.00,30.99],[-80.65,28.17],[-80.36,27.26],[-80.09,26.10],[-80.13,25.77],[-81.08,24.63],[-81.85,24.55],[-82.09,25.12],[-82.17,26.92],[-82.55,27.65],[-83.53,29.13],[-84.08,29.95],[-85.31,29.68],[-85.99,30.18],[-86.40,30.40],[-87.63,30.87]],
  TN:[[-88.05,35.00],[-84.29,34.98],[-83.68,36.60],[-80.29,36.54],[-75.88,36.55],[-77.34,35.97],[-88.05,35.00]],
  KY:[[-89.50,36.50],[-88.05,35.00],[-75.88,36.55],[-77.84,39.13],[-82.58,38.42],[-84.77,38.78],[-89.50,36.50]],
  WV:[[-82.64,38.17],[-81.02,37.45],[-80.52,39.72],[-79.65,39.72],[-77.84,39.13],[-82.64,38.17]],
  MD:[[-79.48,39.72],[-77.46,39.33],[-77.04,38.99],[-76.51,38.53],[-76.06,37.89],[-75.63,37.95],[-75.80,39.48],[-79.48,39.72]],
  DE:[[-75.80,39.48],[-75.63,37.95],[-75.05,38.45],[-75.80,39.48]],
  AL:[[-88.47,35.00],[-85.60,34.98],[-85.00,32.00],[-85.00,31.00],[-87.59,30.99],[-88.10,30.25],[-88.47,35.00]],
  MS:[[-91.65,30.20],[-89.73,30.17],[-88.10,30.25],[-88.47,35.00],[-88.10,34.99],[-91.65,34.99],[-91.65,30.20]],
};

// Map projection bounds — SE US
const MAP_BOUNDS = { latMin:24.3, latMax:39.8, lngMin:-90, lngMax:-74.5 };
// Detention incidents this month
const DETENTION_LOG = [
  { date:"Apr 17", carrier:"PPT", truck:"P-302", site:"Sumter Central Stop",    mins:38, cause:"Site tank full — pump out delay",       cost:57  },
  { date:"Apr 17", carrier:"CCI", truck:"CC-503",site:"Orlando Theme Park",     mins:45, cause:"No attendant — waited for manager",      cost:68  },
  { date:"Apr 16", carrier:"SFT", truck:"T-101", site:"Raleigh North Express",  mins:22, cause:"Equipment issue — hose connection",       cost:33  },
  { date:"Apr 16", carrier:"BRD", truck:"B-401", site:"Richmond Boulevard",     mins:18, cause:"Congested parking — wait for spot",       cost:27  },
  { date:"Apr 17", carrier:"SFT", truck:"T-105", site:"Durham Fuel Depot",      mins:55, cause:"Site tank sensors malfunctioning",        cost:83  },
  { date:"Apr 16", carrier:"CCI", truck:"CC-507",site:"St. Petersburg Bay",     mins:28, cause:"Delayed product release at terminal",     cost:42  },
  { date:"Apr 16", carrier:"PPT", truck:"P-301", site:"Florence I-95 Travel",   mins:72, cause:"Product contamination check — resolved",  cost:108 },
  { date:"Apr 09", carrier:"BRD", truck:"B-402", site:"Arlington Express",      mins:31, cause:"Restricted delivery window — arrived early",cost:47 },
];

// Over/Short reconciliation log (gallons variance between BOL and site meter)
const OVERSHORT_LOG = [
  { date:"Apr 17", bol:"SEL-0887", carrier:"SFT", site:"Cary Crossroads",      grade:"Regular", bol_gals:8000, delivered:7988, variance:-12, varCPG:-0.0015, cause:"Meter variance — within tolerance" },
  { date:"Apr 17", bol:"CLT-0438", carrier:"CFL", site:"Gastonia I-85",        grade:"Diesel",  bol_gals:10000,delivered:10024,variance:+24, varCPG:+0.0024, cause:"Temperature correction — acceptable" },
  { date:"Apr 16", bol:"RIC-0208", carrier:"BRD", site:"Norfolk Harbor Fuel",  grade:"Regular", bol_gals:16000,delivered:15897,variance:-103,varCPG:-0.0064, cause:" SHORT — investigating meter cal" },
  { date:"Apr 16", bol:"ATL-0112", carrier:"AFS", site:"Macon I-75 Center",    grade:"Diesel",  bol_gals:20000,delivered:20011,variance:+11, varCPG:+0.0006, cause:"Within tolerance" },
  { date:"Apr 17", bol:"TPA-0649", carrier:"CCI", site:"Clearwater Beach",     grade:"Regular", bol_gals:14000,delivered:14000,variance:0,   varCPG:0,       cause:"Perfect delivery" },
  { date:"Apr 17", bol:"JAX-0319", carrier:"CCI", site:"Gainesville UF Fuel",  grade:"Diesel",  bol_gals:16000,delivered:15944,variance:-56, varCPG:-0.0035, cause:"Temp-corrected — borderline" },
  { date:"Apr 16", bol:"SEL-0881", carrier:"SFT", site:"Rocky Mount 64 Stop",  grade:"Premium", bol_gals:8000, delivered:8041, variance:+41, varCPG:+0.0051, cause:" LONG — meter audit scheduled" },
];


//  ALTERNATIVE SUPPLY POINTS 
// Non-Colonial sources: Plantation Pipeline, marine/waterborne terminals,
// and truck-only distributor racks. Critical redundancy during Colonial constraints.
const ALT_SUPPLY_TYPES = {
  pipeline:  { label:"Pipeline",   icon:"", color:"#3B82F6" },
  marine:    { label:"Marine",     icon:"", color:"#0EA5E9" },
  truck:     { label:"Truck Rack", icon:"", color:"#8B5CF6" },
  barge:     { label:"Barge",      icon:"", color:"#06B6D4" },
};

const ALT_SUPPLY_POINTS = [
  {
    id:"plantation_atl", name:"Plantation — Doraville", short:"PL-ATL", type:"pipeline", pipeline:"Plantation",
    city:"Doraville", state:"GA", capacity:96.8, status:"NORMAL", leadDays:2,
    rack:{ Regular:3.0012, Premium:3.2312, Diesel:4.5645 },
    tariff:{ gasoline:0.0234, distillate:0.0256 }, freight:0.0356, spotAdder:0.0275,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Apr 25, 12:00 CT",
    notes:"Runs 24-hr cycles — more flexible than Colonial. Good alternative when Colonial Line 1 is constrained.",
    bestFor:["ATL","Charlotte","SC stores"],
  },
  {
    id:"plantation_jax", name:"Plantation — Jacksonville", short:"PL-JAX", type:"pipeline", pipeline:"Plantation",
    city:"Jacksonville", state:"FL", capacity:94.7, status:"NORMAL", leadDays:2,
    rack:{ Regular:3.0578, Premium:3.2878, Diesel:4.6201 },
    tariff:{ gasoline:0.0298, distillate:0.0321 }, freight:0.0298, spotAdder:0.0285,
    allocationActive:false, cycleWindowOpen:false, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Apr 25, 12:00 CT",
    notes:"Plantation primary supply for FL north corridor. Independent of Colonial.",
    bestFor:["JAX","Tallahassee","Gainesville","Pensacola"],
  },
  {
    id:"plantation_tpa", name:"Plantation — Tampa", short:"PL-TPA", type:"pipeline", pipeline:"Plantation",
    city:"Tampa", state:"FL", capacity:95.1, status:"NORMAL", leadDays:2,
    rack:{ Regular:3.0456, Premium:3.2756, Diesel:4.6078 },
    tariff:{ gasoline:0.0321, distillate:0.0345 }, freight:0.0321, spotAdder:0.0285,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Apr 25, 12:00 CT",
    notes:"TPA Plantation terminal serves entire central/south FL corridor.",
    bestFor:["Tampa","Orlando","Clearwater","St. Pete"],
  },
  {
    id:"marine_savannah", name:"Savannah Port Terminal", short:"SAV-MAR", type:"marine", pipeline:null,
    city:"Savannah", state:"GA", capacity:null, status:"AVAILABLE", leadDays:9,
    rack:{ Regular:2.9801, Premium:null, Diesel:4.5523 },
    tariff:null, freight:0.0445, spotAdder:0.0210,
    allocationActive:false, cycleWindowOpen:false, availableGrades:["Regular","Diesel"],
    nominationDeadline:"Next vessel: Apr 26 (7 days)",
    weatherRisk:"Low — protected harbor",
    notes:"Completely independent of Colonial/Plantation. Rack usually $0.02–0.04 below pipeline on tight market days. Premium not typically available.",
    bestFor:["Savannah stores","SC coastal","Macon"],
  },
  {
    id:"marine_charleston", name:"Charleston Harbor Terminal", short:"CHS-MAR", type:"marine", pipeline:null,
    city:"Charleston", state:"SC", capacity:null, status:"AVAILABLE", leadDays:10,
    rack:{ Regular:2.9923, Premium:null, Diesel:4.5567 },
    tariff:null, freight:0.0512, spotAdder:0.0225,
    allocationActive:false, cycleWindowOpen:false, availableGrades:["Regular","Diesel"],
    nominationDeadline:"Next vessel: Apr 25 (9 days)",
    weatherRisk:"Moderate — hurricane season Jun–Nov",
    notes:"Often cheaper than Colonial during allocation periods. No pipeline dependency. Best for SC coastal stores.",
    bestFor:["Charleston","Myrtle Beach","Hilton Head"],
  },
  {
    id:"marine_wilmington", name:"Wilmington NC Marine Terminal", short:"ILM-MAR", type:"marine", pipeline:null,
    city:"Wilmington", state:"NC", capacity:null, status:"AVAILABLE", leadDays:11,
    rack:{ Regular:3.0089, Premium:null, Diesel:4.5612 },
    tariff:null, freight:0.0534, spotAdder:0.0232,
    allocationActive:false, cycleWindowOpen:false, availableGrades:["Regular","Diesel"],
    nominationDeadline:"Next vessel: Apr 26 (10 days)",
    weatherRisk:"Moderate — Cape Fear River restrictions in storms",
    notes:"Critical redundancy for eastern NC. During Colonial disruptions this becomes high-demand — secure vessel slots early.",
    bestFor:["Wilmington","Fayetteville","Rocky Mount"],
  },
  {
    id:"marine_hampton", name:"Hampton Roads Marine Terminal", short:"HRT-MAR", type:"marine", pipeline:null,
    city:"Norfolk", state:"VA", capacity:null, status:"AVAILABLE", leadDays:8,
    rack:{ Regular:3.0234, Premium:null, Diesel:4.5756 },
    tariff:null, freight:0.0478, spotAdder:0.0218,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Diesel"],
    nominationDeadline:"Next vessel: Apr 25 (7 days)",
    weatherRisk:"Low — sheltered deep-water port",
    notes:"One of the deepest natural harbors on the East Coast. Also has Buckeye Pipeline access for inland distribution.",
    bestFor:["Norfolk","VA Beach","Newport News","Chesapeake"],
  },
  {
    id:"marine_miami", name:"Port of Miami Marine Terminal", short:"MIA-MAR", type:"marine", pipeline:null,
    city:"Miami", state:"FL", capacity:null, status:"AVAILABLE", leadDays:7,
    rack:{ Regular:3.0489, Premium:3.2789, Diesel:4.6112 },
    tariff:null, freight:0.0389, spotAdder:0.0198,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Continuous — active spot tanker market",
    weatherRisk:"High — hurricane season risk Jun–Nov",
    notes:"South FL is heavily marine-dependent. Continuous tanker traffic makes lead times shorter. Active spot market. All grades available.",
    bestFor:["Miami","Ft. Lauderdale","South FL stores"],
  },
  {
    id:"truck_raleigh", name:"Raleigh Area Jobber Rack", short:"RDU-TRK", type:"truck", pipeline:null,
    city:"Raleigh", state:"NC", capacity:null, status:"AVAILABLE", leadDays:1,
    rack:{ Regular:3.0712, Premium:3.3012, Diesel:4.6334 },
    tariff:null, freight:0.0623, spotAdder:0.0312,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Same-day by 10:00 AM",
    weatherRisk:"None",
    notes:"Most expensive but fastest. No pipeline dependency. Good for emergency top-ups and small volumes. Delivery to site included in freight.",
    bestFor:["Emergency reorder","Small top-up orders","Pipeline constraint backup"],
  },
  {
    id:"truck_columbia", name:"Columbia SC Distributor Rack", short:"CAE-TRK", type:"truck", pipeline:null,
    city:"Columbia", state:"SC", capacity:null, status:"AVAILABLE", leadDays:1,
    rack:{ Regular:3.0567, Premium:3.2867, Diesel:4.6189 },
    tariff:null, freight:0.0589, spotAdder:0.0298,
    allocationActive:false, cycleWindowOpen:true, availableGrades:["Regular","Premium","Diesel"],
    nominationDeadline:"Same-day by 10:00 AM",
    weatherRisk:"None",
    notes:"Regional distributor serving SC stores. Branded and unbranded product available. Immediate availability vs pipeline scheduling.",
    bestFor:["SC emergency reorder","Small volume top-up","Upstate SC"],
  },
];

function altLandedCost(sp, grade, stateTax) {
  const r = sp.rack[grade];
  if (!r) return null;
  const tariff = sp.tariff ? (grade === "Diesel" ? sp.tariff.distillate : sp.tariff.gasoline) : 0;
  const spot = r + sp.spotAdder + sp.freight + stateTax + FED_TAX;
  const contract = sp.type === "pipeline" ? r + tariff + sp.freight + stateTax + FED_TAX : null;
  return { spot, contract, rack:r };
}





// Ticker items
const TICKER_ITEMS = [
  { label:"ULSD NYMEX", val:`$${NYMEX.ulsd[30].toFixed(4)}/gal`, delta:"+0.0124", up:true },
  { label:"RBOB NYMEX",  val:`$${NYMEX.rbob[30].toFixed(4)}/gal`, delta:"+0.0098", up:true },
  { label:"WTI CRUDE",   val:`$${NYMEX.crude[30].toFixed(2)}/bbl`, delta:"+1.42",   up:true },
  { label:"SEL REGULAR", val:`$${RACK_PRICES.selma.Regular.toFixed(4)}/gal`, delta:"-0.0042", up:false },
  { label:"SEL DIESEL",  val:`$${RACK_PRICES.selma.Diesel.toFixed(4)}/gal`, delta:"+0.0078", up:true },
  { label:"CLT REGULAR", val:`$${RACK_PRICES.charlotte.Regular.toFixed(4)}/gal`, delta:"-0.0051", up:false },
  { label:"RIC REGULAR", val:`$${RACK_PRICES.richmond.Regular.toFixed(4)}/gal`, delta:"+0.0023", up:true },
  { label:"ATL REGULAR", val:`$${RACK_PRICES.atlanta.Regular.toFixed(4)}/gal`, delta:"+0.0017", up:true },
  { label:"JAX DIESEL",  val:`$${RACK_PRICES.jacksonville.Diesel.toFixed(4)}/gal`, delta:"+0.0091", up:true },
  { label:"TPA REGULAR", val:`$${RACK_PRICES.tampa.Regular.toFixed(4)}/gal`, delta:"-0.0038", up:false },
  { label:"NC STATE TAX",val:`$${STATE_TAX.NC.toFixed(4)}/gal`, delta:"—", up:true },
  { label:"FL STATE TAX",val:`$${STATE_TAX.FL.toFixed(4)}/gal`, delta:"—", up:true },
  { label:"COLONIAL L1",  val:`${COLONIAL.line1Capacity}% cap`, delta:COLONIAL.status==="NORMAL"?"Normal":" Alert", up:COLONIAL.line1Capacity>=97 },
  { label:"COLONIAL L2",  val:`${COLONIAL.line2Capacity}% cap`, delta:"Distillates", up:COLONIAL.line2Capacity>=97 },
  { label:"NOM DEADLINE", val:COLONIAL.nominationDeadline, delta:"Line 1 cycle", up:true },
];

//  SPARK LINE 
function Spark({ data, color, h = 36 }) {
  const W = 240, H = h, PAD = 3;
  const min = Math.min(...data), max = Math.max(...data), range = max - min || 0.01;
  const pts = data.map((v, i) => [(i / (data.length - 1)) * (W - PAD*2) + PAD, H - PAD*1.5 - (v - min) / range * (H - PAD*3.5)]);
  const d = pts.map((p, i) => `${i === 0 ? "M" : "L"}${p[0].toFixed(1)},${p[1].toFixed(1)}`).join(" ");
  const area = d + ` L${pts[pts.length-1][0].toFixed(1)},${H} L${pts[0][0].toFixed(1)},${H} Z`;
  const last = pts[pts.length - 1];
  const gid = `sp${color.replace(/[^a-z0-9]/gi,"")}${h}`;
  return (
    <svg width="100%" viewBox={`0 0 ${W} ${H}`} preserveAspectRatio="none" style={{ display: "block" }}>
      <defs><linearGradient id={gid} x1="0" y1="0" x2="0" y2="1">
        <stop offset="0%" stopColor={color} stopOpacity="0.18"/>
        <stop offset="100%" stopColor={color} stopOpacity="0.01"/>
      </linearGradient></defs>
      <path d={area} fill={`url(#${gid})`} stroke="none"/>
      <path d={d} fill="none" stroke={color} strokeWidth="1.2" strokeLinecap="round" strokeLinejoin="round"/>
      <circle cx={last[0]} cy={last[1]} r="2.4" fill={color}/>
    </svg>
  );
}

//  MULTI-LINE CHART 
function MultiLine({ series, h = 80, C, darkMode }) {
  const W = 600, H = h, bt = 6, bb = 16, bl = 38, br = 8;
  const IW = W - bl - br, IH = H - bt - bb;
  const all = series.flatMap(s => s.data);
  const min = Math.min(...all), max = Math.max(...all), range = max - min || 0.01;
  const mkPts = d => d.map((v, i) => [(i / (d.length - 1)) * IW + bl, IH + bt - (v - min) / range * IH]);
  const bd = C.cardBord, tm = C.textMut;
  const FONT = "Arial,sans-serif";
  const labels = ["Mar 17","Mar 24","Apr 16","Apr 17","Apr 16","Apr 16"];
  const labelIdxs = [0, Math.floor((labels.length-1)/3), Math.floor(2*(labels.length-1)/3), labels.length-1];
  const yTicks = [min, (min+max)/2, max];
  return (
    <svg width="100%" viewBox={`0 0 ${W} ${H}`} preserveAspectRatio="none" style={{ display: "block" }}>
      {yTicks.map((v, i) => {
        const y = IH + bt - (v - min) / range * IH;
        return (<g key={i}>
          <line x1={bl} y1={y} x2={W - br} y2={y} stroke={bd} strokeWidth="0.45" strokeDasharray={i===1?"4,6":"none"}/>
          <text x={bl-4} y={y+3.5} textAnchor="end" fontSize="6.5" fill={tm} fontFamily={FONT} fontWeight="700">${v.toFixed(3)}</text>
        </g>);
      })}
      <line x1={bl} y1={bt} x2={bl} y2={IH+bt} stroke={bd} strokeWidth="0.45"/>
      {series.map((s, si) => {
        const pts = mkPts(s.data);
        const dp = pts.map((p, i) => `${i===0?"M":"L"}${p[0].toFixed(1)},${p[1].toFixed(1)}`).join(" ");
        const last = pts[pts.length-1];
        return (<g key={si}>
          <path d={dp} fill="none" stroke={s.color} strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round" strokeDasharray={s.dash||"none"}/>
          <circle cx={last[0]} cy={last[1]} r="2.4" fill={s.color}/>
          <circle cx={last[0]} cy={last[1]} r="5" fill={s.color} fillOpacity="0.15"/>
        </g>);
      })}
      {labelIdxs.map((i, pos) => {
        const n = series[0]?.data?.length || 1;
        const x = (i / (n-1)) * IW + bl;
        const lbl = labels[Math.floor(i/(n-1)*((labels.length-1)))] || "";
        return (<text key={i} x={x} y={H-2} textAnchor={pos===0?"start":pos===labelIdxs.length-1?"end":"middle"} fontSize="6.5" fill={tm} fontFamily={FONT} fontWeight="700">{lbl}</text>);
      })}
    </svg>
  );
}

//  STATUS BADGE 
const STATUS_COLORS = {
  "Dispatched":   { bg:"#EFF6FF", text:"#1D4ED8", border:"#BFDBFE" },
  "En Route":     { bg:"#FFF7ED", text:"#C2410C", border:"#FED7AA" },
  "At Terminal":  { bg:"#F8FAFB", text:"#B45309", border:"#FDE68A" },
  "Loaded":       { bg:"#F0FDF4", text:"#15803D", border:"#BBF7D0" },
  "Delivered":    { bg:"#F0FDF4", text:"#166534", border:"#86EFAC" },
  "Reconciled":   { bg:"#F8FAFC", text:"#475569", border:"#CBD5E1" },
};
const STATUS_COLORS_DARK = {
  "Dispatched":   { bg:"rgba(29,95,168,.18)", text:"#60A5FA", border:"rgba(29,95,168,.35)" },
  "En Route":     { bg:"rgba(194,65,12,.18)", text:"#FB923C", border:"rgba(194,65,12,.35)" },
  "At Terminal":  { bg:"rgba(180,83,9,.18)",  text:"#FCD34D", border:"rgba(180,83,9,.35)" },
  "Loaded":       { bg:"rgba(21,128,61,.18)", text:"#4ADE80", border:"rgba(21,128,61,.35)" },
  "Delivered":    { bg:"rgba(22,101,52,.22)", text:"#86EFAC", border:"rgba(22,101,52,.45)" },
  "Reconciled":   { bg:"rgba(71,85,105,.18)", text:"#94A3B8", border:"rgba(71,85,105,.35)" },
};
function StatusBadge({ status, darkMode }) {
  const sc = darkMode ? STATUS_COLORS_DARK[status] : STATUS_COLORS[status];
  return (
    <span style={{ fontSize:10, fontWeight:700, padding:"2px 8px", borderRadius:20, background:sc?.bg, color:sc?.text, border:`1px solid ${sc?.border}`, whiteSpace:"nowrap", fontFamily:"Arial,sans-serif" }}>
      {status}
    </span>
  );
}

//  GRADE TAG 
const GRADE_COLORS = {
  Regular: { bg:"#EFF6FF", text:"#1D4ED8", border:"#BFDBFE" },
  Premium: { bg:"#F0FDFA", text:"#0D9488", border:"#99F6E4" },
  Diesel:  { bg:"#F8FAFB", text:"#B45309", border:"#FDE68A" },
};
const GRADE_COLORS_DARK = {
  Regular: { bg:"rgba(29,95,168,.2)",  text:"#60A5FA", border:"rgba(29,95,168,.4)" },
  Premium: { bg:"rgba(13,148,136,.2)", text:"#2DD4BF", border:"rgba(13,148,136,.4)" },
  Diesel:  { bg:"rgba(180,83,9,.2)",   text:"#FCD34D", border:"rgba(180,83,9,.4)" },
};
function GradeTag({ grade, darkMode }) {
  const gc = darkMode ? GRADE_COLORS_DARK[grade] : GRADE_COLORS[grade];
  return (
    <span style={{ fontSize:10, fontWeight:700, padding:"2px 8px", borderRadius:20, background:gc?.bg, color:gc?.text, border:`1px solid ${gc?.border}`, fontFamily:"Arial,sans-serif" }}>
      {grade}
    </span>
  );
}

//  SECTION HEADER 
function SectionHeader({ title, sub, action, C }) {
  return (
    <div style={{ display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:12 }}>
      <div>
        <div style={{ fontSize:13, fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif" }}>{title}</div>
        {sub && <div style={{ fontSize:10.5, color:C.textSec, marginTop:2 }}>{sub}</div>}
      </div>
      {action}
    </div>
  );
}

//  KPI CARD 
function KpiCard({ label, value, sub, trend, trendUp, color, C, darkMode, spark }) {
  const cc = color || C.gold;
  return (
    <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:"14px 16px", flex:"1 1 0", minWidth:0, position:"relative", overflow:"hidden" }}>
      <div style={{ fontSize:9.5, fontWeight:700, color:C.textSec, textTransform:"uppercase", letterSpacing:0.8, marginBottom:6, fontFamily:"Arial,sans-serif" }}>{label}</div>
      <div style={{ fontSize:22, fontWeight:800, color:C.textPri, lineHeight:1, fontFamily:"Arial,sans-serif", letterSpacing:-0.5 }}>{value}</div>
      {sub && <div style={{ fontSize:10.5, color:C.textSec, marginTop:4 }}>{sub}</div>}
      {trend && (
        <div style={{ marginTop:6, fontSize:11, fontWeight:700, color:trendUp?C.green:C.red, fontFamily:"Arial,sans-serif" }}>
          {trendUp ? "" : ""} {trend}
        </div>
      )}
      {spark && <div style={{ position:"absolute", bottom:0, left:0, right:0, height:36, opacity:0.45 }}><Spark data={spark} color={cc} h={36}/></div>}
    </div>
  );
}

//  DONUT 
function Donut({ slices, size = 56, thick = 6, C }) {
  const r = (size - thick) / 2, cx = size/2, cy = size/2, circ = 2 * Math.PI * r;
  const tot = slices.reduce((a, x) => a + x.v, 0) || 1;
  let off = 0;
  return (
    <svg width={size} height={size} style={{ flexShrink:0 }}>
      <circle cx={cx} cy={cy} r={r} fill="none" stroke={C.cardBord} strokeWidth={thick}/>
      {slices.map((sl, i) => {
        const pct = sl.v / tot, dash = circ * pct, gap = circ * (1 - pct);
        const el = <circle key={i} cx={cx} cy={cy} r={r} fill="none" stroke={sl.color} strokeWidth={thick} strokeDasharray={`${dash} ${gap}`} strokeDashoffset={-off * circ} style={{ transform:"rotate(-90deg)", transformOrigin:`${cx}px ${cy}px` }}/>;
        off += pct; return el;
      })}
    </svg>
  );
}

//  INVENTORY BAR 
function InvBar({ pct, color, C }) {
  const p = Math.min(100, Math.max(0, pct * 100));
  const barColor = p < 25 ? "#EF4444" : p < 50 ? "#F59E0B" : color;
  return (
    <div style={{ height:5, background:C.cardBord, borderRadius:3, overflow:"hidden", width:"100%" }}>
      <div style={{ height:"100%", width:`${p}%`, background:barColor, borderRadius:3, transition:"width .3s" }}/>
    </div>
  );
}

//  MAIN APP 

// 
// PROCUREMENT MODULE DATA
// 

//  Supplier Database 
const SUPPLIERS = [
  {
    id:"sup1", name:"Valero Marketing & Supply", short:"Valero",
    type:"Refiner", tier:1, // tier 1 = direct refiner, 2 = jobber, 3 = spot-only
    contacts:[
      {name:"Derek Holt",     role:"Account Manager",  phone:"210-555-0142", email:"dholt@valero.com"},
      {name:"Lisa Crane",     role:"Credit Manager",   phone:"210-555-0199", email:"lcrane@valero.com"},
    ],
    terminals:["selma","atlanta"],
    grades:["Regular","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 10", creditLimit:2500000,
    ytdVolume:4120000, ytdSpend:10940000,
    contractExpiry:"Dec 31 2025", contractType:"Annual Volume",
    minMonthlyVol:600000,
    performanceScore:94,
    incidents:0,
    notes:"Primary supplier SEL + ATL. Strong rack position on Diesel. Negotiate Premium uplift Q3.",
  },
  {
    id:"sup2", name:"Shell Oil Products US", short:"Shell",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Amanda Torres",  role:"Account Manager",  phone:"713-555-0271", email:"atorres@shell.com"},
      {name:"Greg Paulsen",   role:"Logistics",        phone:"713-555-0388", email:"gpaulsen@shell.com"},
    ],
    terminals:["charlotte","jacksonville"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 7", creditLimit:3000000,
    ytdVolume:5340000, ytdSpend:14230000,
    contractExpiry:"Jun 30 2026", contractType:"Annual Volume",
    minMonthlyVol:700000,
    performanceScore:97,
    incidents:0,
    notes:"Best Premium availability in CLT. New 18-month contract locked pricing advantage through mid-2026.",
  },
  {
    id:"sup3", name:"ExxonMobil Fuels & Lubricants", short:"ExxonMobil",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Paul Sheridan",  role:"Account Manager",  phone:"972-555-0312", email:"psheridan@exxon.com"},
      {name:"Karen Yost",     role:"Credit & Risk",    phone:"972-555-0451", email:"kyost@exxon.com"},
    ],
    terminals:["richmond","tampa"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 10", creditLimit:2800000,
    ytdVolume:3980000, ytdSpend:10620000,
    contractExpiry:"Apr 2 2026", contractType:"Annual Volume",
    minMonthlyVol:550000,
    performanceScore:91,
    incidents:1,
    notes:"RIC supply tight in winter — maintain 30-day forward coverage. TPA performance excellent.",
  },
  {
    id:"sup4", name:"Motiva Enterprises", short:"Motiva",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Frank Deluca",   role:"Supply Manager",   phone:"713-555-0198", email:"fdeluca@motiva.com"},
    ],
    terminals:["selma","charlotte"],
    grades:["Regular","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 10", creditLimit:1500000,
    ytdVolume:1240000, ytdSpend:3290000,
    contractExpiry:"Rolling 90-day", contractType:"Preferred Spot",
    minMonthlyVol:0,
    performanceScore:88,
    incidents:0,
    notes:"Secondary supplier — use when primary constrained or spot dips below contract. Good Colonial access.",
  },
  {
    id:"sup5", name:"Sunoco LP", short:"Sunoco",
    type:"Jobber", tier:2,
    contacts:[
      {name:"Ray Kowalski",   role:"Account Rep",      phone:"215-555-0144", email:"rkowalski@sunoco.com"},
    ],
    terminals:["richmond","charlotte"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"Posted price + margin",
    creditTerms:"Net 14", creditLimit:800000,
    ytdVolume:680000, ytdSpend:1820000,
    contractExpiry:"Month-to-month", contractType:"Spot / Jobber",
    minMonthlyVol:0,
    performanceScore:82,
    incidents:2,
    notes:"Use for emergency coverage or small top-ups. 2 delivery incidents YTD — monitor O/S closely.",
  },
  {
    id:"sup6", name:"Gulf Oil LP", short:"Gulf",
    type:"Jobber", tier:2,
    contacts:[
      {name:"Dana Ricci",     role:"Sales Director",   phone:"617-555-0231", email:"dricci@gulfoil.com"},
    ],
    terminals:["jacksonville","tampa"],
    grades:["Regular","Diesel"],
    pricingBasis:"OPIS Rack + margin",
    creditTerms:"Net 10", creditLimit:600000,
    ytdVolume:540000, ytdSpend:1430000,
    contractExpiry:"Dec 31 2025", contractType:"Preferred Spot",
    minMonthlyVol:0,
    performanceScore:85,
    incidents:1,
    notes:"Solid FL backup. Better diesel rack than primary on ~30% of trading days. Worth daily comparison.",
  },
  {
    id:"sup7", name:"Marathon Petroleum", short:"MPC",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Brian Caulfield", role:"Account Manager",  phone:"419-555-0183", email:"bcaulfield@marathonpetroleum.com"},
      {name:"Stacy Horn",      role:"Credit Manager",   phone:"419-555-0247", email:"shorn@marathonpetroleum.com"},
    ],
    terminals:["selma","richmond","atlanta","jacksonville","tampa"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 10", creditLimit:3500000,
    ytdVolume:7240000, ytdSpend:19180000,
    contractExpiry:"Dec 31 2026", contractType:"Annual Volume",
    minMonthlyVol:800000,
    performanceScore:96,
    incidents:0,
    notes:"Largest volume supplier in portfolio. Strong presence across all Colonial terminals. Excellent on-time record — leverage for Q3 pricing renegotiation.",
  },
  {
    id:"sup8", name:"Citgo Petroleum", short:"CITGO",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Marco Villareal", role:"Supply Manager",   phone:"832-555-0309", email:"mvillareal@citgo.com"},
    ],
    terminals:["atlanta","tampa"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 7", creditLimit:2000000,
    ytdVolume:2890000, ytdSpend:7640000,
    contractExpiry:"Mar 31 2026", contractType:"Annual Volume",
    minMonthlyVol:400000,
    performanceScore:90,
    incidents:0,
    notes:"Competitive on ATL and TPA diesel. Contract renewal due — initiate discussions. Explore Premium uplift availability for summer blend.",
  },
  {
    id:"sup9", name:"BP Products", short:"BP",
    type:"Refiner", tier:1,
    contacts:[
      {name:"Claire Ashworth", role:"Account Director", phone:"312-555-0417", email:"cashworth@bp.com"},
      {name:"Tom Nguyen",      role:"Logistics",        phone:"312-555-0522", email:"tnguyen@bp.com"},
    ],
    terminals:["charlotte"],
    grades:["Regular","Premium","Diesel"],
    pricingBasis:"OPIS Rack + differential",
    creditTerms:"Net 10", creditLimit:2200000,
    ytdVolume:1980000, ytdSpend:5260000,
    contractExpiry:"Sep 30 2026", contractType:"Annual Volume",
    minMonthlyVol:350000,
    performanceScore:93,
    incidents:0,
    notes:"Primary CLT supplier for Premium. Reliable Plantation access. Spot frequently competitive — check daily vs contract before routing.",
  },
];

//  Purchase Orders 
const PURCHASE_ORDERS_DATA = [
  { id:"PO-2504-001", supplierId:"sup1", terminal:"selma",    grade:"Regular", gals:120000, pricePerGal:3.0424, totalCost:365088, status:"CONFIRMED",  created:"Apr 16", delivery:"Apr 16-18", invoiced:false,  notes:"3-day lift window on Colonial L1" },
  { id:"PO-2504-002", supplierId:"sup2", terminal:"charlotte",grade:"Premium", gals:45000,  pricePerGal:3.2723, totalCost:147253, status:"LOADING",    created:"Apr 17", delivery:"Apr 16",    invoiced:false,  notes:"Window open — loading today" },
  { id:"PO-2504-003", supplierId:"sup3", terminal:"richmond", grade:"Diesel",  gals:80000,  pricePerGal:4.6501, totalCost:372008, status:"CONFIRMED",  created:"Apr 17", delivery:"Apr 15-17", invoiced:false,  notes:"Line 2 at 94.7% — confirm before lift" },
  { id:"PO-2504-004", supplierId:"sup2", terminal:"jacksonville",grade:"Regular",gals:95000,pricePerGal:3.0957, totalCost:294091, status:"DRAFT",     created:"Apr 16", delivery:"Apr 17-18", invoiced:false,  notes:"Pending nomination approval" },
  { id:"PO-2504-005", supplierId:"sup1", terminal:"atlanta",  grade:"Diesel",  gals:60000,  pricePerGal:4.6001, totalCost:276006, status:"DELIVERED", created:"Apr 16", delivery:"Apr 16",    invoiced:true,   notes:"Delivered — O/S within tolerance" },
  { id:"PO-2504-006", supplierId:"sup3", terminal:"tampa",    grade:"Regular", gals:110000, pricePerGal:3.0713, totalCost:337843, status:"DELIVERED", created:"Apr 09", delivery:"Apr 17",    invoiced:true,   notes:"CCI carrier — clean delivery" },
  { id:"PO-2504-007", supplierId:"sup4", terminal:"selma",    grade:"Regular", gals:50000,  pricePerGal:3.011, totalCost:150550, status:"PENDING",   created:"Apr 16", delivery:"Apr 18-19", invoiced:false,  notes:"Motiva spot — $(0.015 below Valero contract today)" },
];

//  Price Alerts 
const PRICE_ALERTS_DATA = [
  { id:"al1", terminal:"selma",     grade:"Regular", type:"ABOVE",  threshold:3.05, active:true,  triggered:false, note:"Alert if SEL Regular exceeds $3.05 — triggers spot evaluation" },
  { id:"al2", terminal:"selma",     grade:"Diesel",  type:"BELOW",  threshold:4.50, active:true,  triggered:true,  note:"BUY signal — diesel below $4.50 threshold" },
  { id:"al3", terminal:"charlotte", grade:"Regular", type:"CHANGE", threshold:0.02, active:true,  triggered:false, note:"Alert on any 1-day move >$0.02 either direction" },
  { id:"al4", terminal:"richmond",  grade:"Diesel",  type:"ABOVE",  threshold:4.65, active:true,  triggered:false, note:"Risk threshold — evaluate marine alternative above $4.65" },
  { id:"al5", terminal:"atlanta",   grade:"Regular", type:"BELOW",  threshold:2.95, active:false, triggered:false, note:"Inactive — ATL spot contract currently cheaper" },
];

//  Hedging positions (Phase 2 scaffold) 
const HEDGE_POSITIONS = [
  { id:"h1", type:"SWAP",    commodity:"ULSD", volume:500000, strike:4.1200, expiry:"May 31 2026", mtm:+18400,  status:"ACTIVE", counterparty:"BP Energy" },
  { id:"h2", type:"CAP",     commodity:"RBOB", volume:300000, strike:2.6500, expiry:"Jun 30 2026", mtm:-4200,   status:"ACTIVE", counterparty:"Macquarie" },
  { id:"h3", type:"COLLAR",  commodity:"ULSD", volume:200000, strike:4.08,   expiry:"Apr 30 2026", mtm:+2100,   status:"EXPIRING", counterparty:"BP Energy" },
];


const TABS = [
  // Grouped into two sections — Operations (what's happening / what to do) and
  // Procurement (what to pay / who to buy from). Sidebar renders a section
  // heading before the first tab of each section when expanded.
  { id:"command",     section:"Operations",  label:"Command",       subtitle:"What needs fuel today" },
  { id:"plan",        section:"Operations",  label:"Plan",          subtitle:"Today's optimised load plan" },
  { id:"replenmap",   section:"Operations",  label:"Store Map",     subtitle:"Where each store stands" },
  { id:"inventory",   section:"Operations",  label:"Inventory",     subtitle:"Tank levels & days of cover" },
  { id:"dispatch",    section:"Operations",  label:"Dispatch",      subtitle:"Trucks, drivers & loads" },
  { id:"bestbuy",     section:"Procurement", label:"Today's Best Buy", subtitle:"Cheapest supplier per terminal-grade" },
  { id:"rack",        section:"Procurement", label:"Rack Prices",   subtitle:"Wholesale prices by terminal" },
  { id:"contracts",   section:"Procurement", label:"Contracts",     subtitle:"Commitment tracking & shortfall risk" },
  { id:"forecast",    section:"Procurement", label:"Forecast",      subtitle:"Price & demand outlook" },
  { id:"procurement", section:"Procurement", label:"Suppliers",     subtitle:"POs, contracts, sourcing" },
  { id:"strategy",    section:"Procurement", label:"Strategy",      subtitle:"Contract vs. spot decisions" },
  { id:"pricing",     section:"Procurement", label:"Street Pricing",subtitle:"Retail price & margin" },
];

// Looked up by tab id so page headers and the tour can reference it.
const TAB_BY_ID = Object.fromEntries(TABS.map(t=>[t.id,t]));

// ── Replenishment Map — D3 Mercator + real TopoJSON state shapes ────────────
// Styled to match the RD Profitability Suite: flat dark navy / soft gray
// basemap, real state polygons loaded from us-atlas, pan/zoom with d3.zoom,
// glassmorphic zoom controls, centroid state labels, drop-shadow terminals.
const MAP_W = 760, MAP_H = 560;
function ReplenMap({ critical, urgent, reorder, darkMode, C, FONT }) {
  const critIds  = useMemo(()=>new Set(critical.map(d=>d.storeId)),[critical]);
  const urgIds   = useMemo(()=>new Set(urgent.map(d=>d.storeId)),[urgent]);
  const reordIds = useMemo(()=>new Set(reorder.map(d=>d.storeId)),[reorder]);

  // Depletion detail lookup — so the tooltip can show days-to-critical
  const detailById = useMemo(()=>{
    const m = new Map();
    critical.forEach(d=>m.set(d.storeId,{bucket:"CRITICAL",...d}));
    urgent.forEach(d=>m.set(d.storeId,{bucket:"URGENT",...d}));
    reorder.forEach(d=>m.set(d.storeId,{bucket:"REORDER",...d}));
    return m;
  },[critical,urgent,reorder]);

  const svgRef = useRef(null);
  const [features, setFeatures] = useState([]);
  const [proj, setProj]         = useState(null);
  const [pathGen, setPathGen]   = useState(null);
  const [mapStatus, setMapStatus] = useState("loading"); // loading | ok | error
  const [zoomT, setZoomT] = useState({x:0,y:0,k:1});
  const [hovered, setHovered] = useState(null); // store object
  const [hoveredTerm, setHoveredTerm] = useState(null);
  const [mousePos, setMousePos] = useState({x:0,y:0});

  // Load state topology from CDN — with fallback mirror
  useEffect(()=>{
    const URLS = [
      "https://cdn.jsdelivr.net/npm/us-atlas@3/states-10m.json",
      "https://unpkg.com/us-atlas@3/states-10m.json",
    ];
    let cancelled = false;
    (async()=>{
      for (const url of URLS) {
        try {
          const res = await fetch(url); if (!res.ok) continue;
          const topo = await res.json();
          if (cancelled) return;
          const all = topoFeatures(topo, "states");
          const filtered = all.filter(f=>SE_SHOW_FIPS.has(String(f.id).padStart(2,"0")));
          const fc = { type:"FeatureCollection", features:filtered };
          const p  = d3.geoMercator().fitExtent([[12,12],[MAP_W-12,MAP_H-12]], fc);
          const pg = d3.geoPath().projection(p);
          setFeatures(filtered); setProj(()=>p); setPathGen(()=>pg); setMapStatus("ok");
          return;
        } catch (e) { console.warn("ReplenMap topology load failed:", url, e.message); }
      }
      if (!cancelled) setMapStatus("error");
    })();
    return ()=>{ cancelled = true; };
  }, []);

  // Attach d3.zoom behaviour
  useEffect(()=>{
    if (!svgRef.current || mapStatus!=="ok") return;
    const zoom = d3.zoom().scaleExtent([0.8, 12]).on("zoom", (event)=>{
      const { x, y, k } = event.transform;
      setZoomT({ x, y, k });
    });
    d3.select(svgRef.current).call(zoom);
    svgRef.current.__zoom_instance = zoom;
    return ()=>{ if (svgRef.current) d3.select(svgRef.current).on(".zoom", null); };
  }, [mapStatus]);

  // Basemap colors — mirror the RD map palette
  const bgFill         = darkMode ? "#0D1421" : "#E8EAED";
  const stateFillMkt   = darkMode ? "#1A2B45" : "#FFFFFF";
  const stateFillOther = darkMode ? "#111D2E" : "#D4D8DE";
  const stateStroke    = darkMode ? "#253650" : "#B4BAC2";
  const labelColMkt    = darkMode ? "#4A7AA0" : "#8A96A4";
  const labelColOther  = darkMode ? "#253650" : "#A8AEB6";

  // Store dot styling based on status bucket
  const storeStyle = (id) => {
    if (critIds.has(id))  return { color:"#EF4444", r:7.5, strokeWidth:1.4, pulse:true };
    if (urgIds.has(id))   return { color:"#F59E0B", r:6,   strokeWidth:1.1, pulse:false };
    if (reordIds.has(id)) return { color:"#F4D398", r:5,   strokeWidth:0.9, pulse:false };
    return { color:"#22C55E", r:3.4, strokeWidth:0.6, pulse:false };
  };

  // Legend chips shown top-right
  const legend = [
    {c:"#EF4444", l:"Critical"},
    {c:"#F59E0B", l:"Urgent"},
    {c:"#F4D398", l:"Reorder"},
    {c:"#22C55E", l:"OK"},
  ];

  // Zoom button handlers
  const doZoom = (factor) => {
    if (!svgRef.current || !svgRef.current.__zoom_instance) return;
    d3.select(svgRef.current).transition().duration(250)
      .call(svgRef.current.__zoom_instance.scaleBy, factor);
  };
  const resetZoom = () => {
    if (!svgRef.current || !svgRef.current.__zoom_instance) return;
    d3.select(svgRef.current).transition().duration(350)
      .call(svgRef.current.__zoom_instance.transform, d3.zoomIdentity);
  };

  const onSvgMouseMove = (e) => {
    if (!svgRef.current) return;
    const rect = svgRef.current.getBoundingClientRect();
    setMousePos({ x: e.clientX - rect.left, y: e.clientY - rect.top });
  };

  return (
    <div style={{
      background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,
      overflow:"hidden",flex:1,display:"flex",flexDirection:"column",position:"relative"
    }}>
      {/* Header */}
      <div style={{
        padding:"10px 14px",borderBottom:`1px solid ${C.cardBord}`,
        display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0
      }}>
        <div style={{display:"flex",alignItems:"center",gap:8}}>
          <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,letterSpacing:.3}}>
            Store Portfolio — Replenishment Status
          </div>
          <div style={{fontSize:10,color:C.textMut,fontFamily:FONT}}>
            · {STORES.length} stores · {TERMINALS.length} terminals
          </div>
        </div>
        <div style={{display:"flex",gap:10}}>
          {legend.map((x,i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:4,fontSize:10,color:C.textSec,fontFamily:FONT}}>
              <div style={{width:8,height:8,borderRadius:"50%",background:x.c,
                boxShadow:x.c==="#EF4444"?`0 0 6px ${x.c}99`:"none"}}/>
              {x.l}
            </div>
          ))}
        </div>
      </div>

      {/* Map surface */}
      <div style={{position:"relative",flex:1,minHeight:400,background:bgFill}}>
        {/* Loading / error overlay */}
        {mapStatus!=="ok" && (
          <div style={{position:"absolute",inset:0,display:"flex",alignItems:"center",justifyContent:"center",
            color:C.textSec,fontSize:12,fontFamily:FONT,zIndex:5,background:bgFill}}>
            {mapStatus==="loading" ? "Loading basemap…" : "Map unavailable — check network"}
          </div>
        )}

        <svg ref={svgRef} width="100%" height="100%"
          viewBox={`0 0 ${MAP_W} ${MAP_H}`}
          preserveAspectRatio="xMidYMid meet"
          onMouseMove={onSvgMouseMove}
          style={{display:"block",cursor:"grab",background:bgFill}}>
          <defs>
            <filter id="rm_dshadow" x="-40%" y="-40%" width="180%" height="180%">
              <feDropShadow dx="0" dy="2" stdDeviation="2.5" floodColor="#000" floodOpacity="0.22"/>
            </filter>
            <filter id="rm_glow" x="-100%" y="-100%" width="300%" height="300%">
              <feGaussianBlur stdDeviation="3" result="b"/>
              <feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge>
            </filter>
            <marker id="rm_arrow" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto">
              <path d="M0,0 L0,7 L7,3.5 Z" fill="#F4D398" fillOpacity="0.9"/>
            </marker>
          </defs>

          {/* Flat basemap fill */}
          <rect width={MAP_W} height={MAP_H} fill={bgFill}/>

          {/* Zoom + pan transform group */}
          <g transform={`translate(${zoomT.x},${zoomT.y}) scale(${zoomT.k})`}>
            {/* State fills */}
            {pathGen && features.map((ft,i)=>{
              const fips = String(ft.id).padStart(2,"0");
              const isMkt = SE_MARKET_FIPS.has(fips);
              return (
                <path key={i} d={pathGen(ft)||""}
                  fill={isMkt?stateFillMkt:stateFillOther}
                  stroke={stateStroke} strokeWidth={0.7}/>
              );
            })}
            {/* State labels (centroids) */}
            {pathGen && features.map((ft,i)=>{
              const fips = String(ft.id).padStart(2,"0");
              const abbr = SE_FIPS_ABBR[fips]; if (!abbr) return null;
              const c = pathGen.centroid(ft); if (!c || isNaN(c[0])) return null;
              const isMkt = SE_MARKET_FIPS.has(fips);
              return (
                <text key={`l${i}`} x={c[0]} y={c[1]+1} textAnchor="middle"
                  fill={isMkt?labelColMkt:labelColOther}
                  fontSize={10} fontWeight={700} letterSpacing={1.3}
                  style={{pointerEvents:"none",userSelect:"none",fontFamily:"Arial,sans-serif"}}>
                  {abbr}
                </text>
              );
            })}

            {/* Colonial + Plantation pipeline routes — real waypoints */}
            {proj && (()=>{
              const routes = [
                { pts:COLONIAL_ROUTE,   color:"#F4D398", label:"Colonial"   },
                { pts:PLANTATION_ROUTE, color:"#3E6387", label:"Plantation" },
              ];
              return routes.map((r,i)=>{
                const poly = r.pts.map(([lng,lat])=>{
                  const p = proj([lng,lat]); return p?`${p[0].toFixed(1)},${p[1].toFixed(1)}`:null;
                }).filter(Boolean).join(" ");
                if (!poly) return null;
                return (
                  <g key={`rt${i}`}>
                    {/* Casing */}
                    <polyline points={poly} fill="none" stroke={darkMode?"#000":"#fff"}
                      strokeWidth={3.2} strokeOpacity={0.25} strokeLinecap="round" strokeLinejoin="round"/>
                    {/* Main */}
                    <polyline points={poly} fill="none" stroke={r.color}
                      strokeWidth={1.6} strokeOpacity={0.85} strokeLinecap="round" strokeLinejoin="round"
                      strokeDasharray="6,4">
                      <animate attributeName="stroke-dashoffset" from="0" to="-20" dur="2.2s" repeatCount="indefinite"/>
                    </polyline>
                  </g>
                );
              });
            })()}

            {/* OK stores — drawn first so they sit under alert dots */}
            {proj && STORES.filter(s=>!critIds.has(s.id)&&!urgIds.has(s.id)&&!reordIds.has(s.id)).map(s=>{
              const p = proj([s.lng, s.lat]); if (!p || isNaN(p[0])) return null;
              const st = storeStyle(s.id);
              const isHov = hovered?.id===s.id;
              return (
                <g key={`s${s.id}`} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}
                  style={{cursor:"pointer"}}
                  onMouseEnter={()=>setHovered(s)} onMouseLeave={()=>setHovered(null)}>
                  {isHov && <circle r={st.r+4} fill="none" stroke={st.color} strokeWidth={1.2} strokeOpacity={0.5}/>}
                  <circle r={st.r+1} fill={darkMode?"#0D1421":"#fff"} opacity={0.9}/>
                  <circle r={st.r} fill={st.color} fillOpacity={0.7}
                    stroke={darkMode?"rgba(255,255,255,.35)":"rgba(13,22,40,.25)"} strokeWidth={st.strokeWidth}/>
                </g>
              );
            })}

            {/* Reorder — gold */}
            {proj && reorder.map(d=>{
              const s = STORES.find(x=>x.id===d.storeId); if (!s) return null;
              const p = proj([s.lng, s.lat]); if (!p || isNaN(p[0])) return null;
              const st = storeStyle(s.id);
              const isHov = hovered?.id===s.id;
              return (
                <g key={`r${s.id}`} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}
                  style={{cursor:"pointer"}}
                  onMouseEnter={()=>setHovered(s)} onMouseLeave={()=>setHovered(null)}>
                  {isHov && <circle r={st.r+6} fill="none" stroke={st.color} strokeWidth={1.4} strokeOpacity={0.55}/>}
                  <circle r={st.r+1.5} fill={darkMode?"#0D1421":"#fff"}/>
                  <circle r={st.r} fill={st.color} stroke="#fff" strokeWidth={st.strokeWidth}/>
                </g>
              );
            })}

            {/* Urgent — amber */}
            {proj && urgent.map(d=>{
              const s = STORES.find(x=>x.id===d.storeId); if (!s) return null;
              const p = proj([s.lng, s.lat]); if (!p || isNaN(p[0])) return null;
              const st = storeStyle(s.id);
              const isHov = hovered?.id===s.id;
              return (
                <g key={`u${s.id}`} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}
                  style={{cursor:"pointer"}}
                  onMouseEnter={()=>setHovered(s)} onMouseLeave={()=>setHovered(null)}>
                  {isHov && <circle r={st.r+6} fill="none" stroke={st.color} strokeWidth={1.5} strokeOpacity={0.6}/>}
                  <circle r={st.r+1.5} fill={darkMode?"#0D1421":"#fff"}/>
                  <circle r={st.r} fill={st.color} stroke="#fff" strokeWidth={st.strokeWidth}/>
                </g>
              );
            })}

            {/* Critical — red, with pulsing halo */}
            {proj && critical.map(d=>{
              const s = STORES.find(x=>x.id===d.storeId); if (!s) return null;
              const p = proj([s.lng, s.lat]); if (!p || isNaN(p[0])) return null;
              const st = storeStyle(s.id);
              const isHov = hovered?.id===s.id;
              return (
                <g key={`c${s.id}`} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}
                  style={{cursor:"pointer"}}
                  onMouseEnter={()=>setHovered(s)} onMouseLeave={()=>setHovered(null)}>
                  {/* Pulsing halo */}
                  <circle r={st.r+5} fill="none" stroke={st.color} strokeWidth={1.6} strokeOpacity={0.85}>
                    <animate attributeName="r" values={`${st.r+3};${st.r+10};${st.r+3}`} dur="1.8s" repeatCount="indefinite"/>
                    <animate attributeName="stroke-opacity" values="0.85;0;0.85" dur="1.8s" repeatCount="indefinite"/>
                  </circle>
                  {isHov && <circle r={st.r+7} fill="none" stroke={st.color} strokeWidth={1.6} strokeOpacity={0.55}/>}
                  <circle r={st.r+2} fill={darkMode?"#0D1421":"#fff"}/>
                  <circle r={st.r} fill={st.color} stroke="#fff" strokeWidth={st.strokeWidth}
                    filter="url(#rm_glow)"/>
                </g>
              );
            })}

            {/* Terminals — gold diamond markers on top of everything */}
            {proj && TERMINALS.map(t=>{
              const p = proj([t.lng, t.lat]); if (!p || isNaN(p[0])) return null;
              const isHov = hoveredTerm?.id===t.id;
              return (
                <g key={`t${t.id}`} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}
                  style={{cursor:"pointer"}}
                  onMouseEnter={()=>setHoveredTerm(t)} onMouseLeave={()=>setHoveredTerm(null)}>
                  {isHov && <circle r={16} fill="none" stroke="#F4D398" strokeWidth={1.4} strokeOpacity={0.6}/>}
                  {/* Outer glow ring */}
                  <circle r={12} fill={darkMode?"#0D1421":"#fff"} stroke="#F4D398" strokeWidth={2.5}
                    filter="url(#rm_dshadow)"/>
                  {/* Inner diamond */}
                  <rect x={-4} y={-4} width={8} height={8} fill="#F4D398" transform="rotate(45)"/>
                  <text y={22} textAnchor="middle" fontSize={9}
                    fill={darkMode?"#F4D398":"#8B6914"}
                    fontFamily="Arial,sans-serif" fontWeight={800}
                    style={{pointerEvents:"none",userSelect:"none",letterSpacing:.4}}>
                    {t.short}
                  </text>
                </g>
              );
            })}
          </g>
        </svg>

        {/* Glassmorphic zoom controls — bottom-right */}
        {mapStatus==="ok" && (
          <div style={{position:"absolute",bottom:12,right:12,display:"flex",flexDirection:"column",gap:3,zIndex:10}}>
            {[
              { label:"+", title:"Zoom in",  fn:()=>doZoom(1.5) },
              { label:"−", title:"Zoom out", fn:()=>doZoom(1/1.5) },
              { label:"⊙", title:"Reset",    fn:resetZoom },
            ].map(btn=>(
              <button key={btn.label} title={btn.title} onClick={btn.fn}
                style={{
                  width:30,height:30,borderRadius:7,
                  border:`1px solid ${darkMode?"rgba(255,255,255,.1)":"rgba(255,255,255,.85)"}`,
                  background:darkMode?"rgba(4,14,26,.78)":"rgba(255,255,255,.78)",
                  backdropFilter:"blur(10px)",WebkitBackdropFilter:"blur(10px)",
                  color:darkMode?"#6A9DC0":C.textSec,
                  fontSize:17,fontWeight:700,cursor:"pointer",
                  display:"flex",alignItems:"center",justifyContent:"center",lineHeight:1,
                  boxShadow:"0 2px 8px rgba(0,0,0,.22)",fontFamily:"Arial,sans-serif",
                }}>
                {btn.label}
              </button>
            ))}
          </div>
        )}

        {/* Glassmorphic counts chip — top-left */}
        {mapStatus==="ok" && (
          <div style={{
            position:"absolute",top:10,left:10,zIndex:10,
            display:"flex",alignItems:"center",gap:10,
            padding:"6px 12px",borderRadius:20,
            background:darkMode?"rgba(13,22,39,.80)":"rgba(255,255,255,.85)",
            border:`1px solid ${darkMode?"#1E3A5A":"#CBD5E1"}`,
            boxShadow:"0 2px 8px rgba(0,0,0,.25)",
            backdropFilter:"blur(10px)",WebkitBackdropFilter:"blur(10px)",
          }}>
            {[
              { n:critical.length, c:"#EF4444", l:"critical" },
              { n:urgent.length,   c:"#F59E0B", l:"urgent" },
              { n:reorder.length,  c:"#F4D398", l:"reorder" },
            ].map((s,i)=>(
              <div key={i} style={{display:"flex",alignItems:"center",gap:5,fontSize:10.5,fontWeight:600,color:darkMode?"#7B9EBE":C.textSec,fontFamily:FONT}}>
                <span style={{
                  display:"inline-flex",alignItems:"center",justifyContent:"center",
                  minWidth:18,height:18,padding:"0 5px",borderRadius:9,
                  background:s.c,color:"#fff",fontSize:10,fontWeight:800,
                  fontFamily:"Arial,sans-serif",
                }}>{s.n}</span>
                {s.l}
              </div>
            ))}
          </div>
        )}

        {/* Store tooltip — positioned near mouse */}
        {hovered && (()=>{
          const d = detailById.get(hovered.id);
          const bucket = d?.bucket || "OK";
          const bucketColor = bucket==="CRITICAL"?"#EF4444"
            : bucket==="URGENT"?"#F59E0B"
            : bucket==="REORDER"?"#F4D398":"#22C55E";
          const term = TERMINALS.find(t=>t.id===hovered.terminal);
          const flipLeft = mousePos.x > (svgRef.current?.getBoundingClientRect().width || MAP_W) * 0.65;
          const tipW = 230;
          return (
            <div style={{
              position:"absolute",
              left: flipLeft ? mousePos.x - tipW - 14 : mousePos.x + 14,
              top:  mousePos.y - 10,
              width:tipW,zIndex:20,pointerEvents:"none",
              background:darkMode?"rgba(11,14,22,.95)":"rgba(255,255,255,.98)",
              border:`1px solid ${darkMode?"#1E3A5A":"#CBD5E1"}`,
              borderRadius:8,boxShadow:"0 8px 24px rgba(0,0,0,.28)",
              backdropFilter:"blur(12px)",WebkitBackdropFilter:"blur(12px)",
              fontFamily:FONT,overflow:"hidden",
            }}>
              <div style={{padding:"8px 12px",borderBottom:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`}}>
                <div style={{fontSize:11.5,fontWeight:700,color:C.textPri,lineHeight:1.25}}>{hovered.name}</div>
                <div style={{fontSize:10,color:C.textMut,marginTop:2}}>{hovered.city}, {hovered.state}</div>
              </div>
              <div style={{padding:"8px 12px",display:"flex",alignItems:"center",justifyContent:"space-between",gap:8}}>
                <span style={{fontSize:9.5,fontWeight:800,letterSpacing:.5,
                  color:"#fff",background:bucketColor,padding:"2px 7px",borderRadius:4,fontFamily:"Arial,sans-serif"}}>
                  {bucket}
                </span>
                {d && (
                  <span style={{fontSize:10.5,color:C.textSec,fontWeight:600,fontFamily:"Arial,sans-serif"}}>
                    {d.minCritical!=null && d.minCritical<=7 ? `${d.minCritical}d to critical` : `${d.minReorder}d to reorder`}
                  </span>
                )}
              </div>
              {term && (
                <div style={{padding:"6px 12px",borderTop:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`,
                  background:darkMode?"#0B0E16":"#FAFBFD",display:"flex",alignItems:"center",gap:6}}>
                  <div style={{width:6,height:6,borderRadius:"50%",background:"#F4D398"}}/>
                  <span style={{fontSize:10,color:C.textMut}}>Supplied from</span>
                  <span style={{fontSize:10,fontWeight:700,color:C.textSec,fontFamily:"Arial,sans-serif"}}>{term.short} · {term.name}</span>
                </div>
              )}
            </div>
          );
        })()}

        {/* Terminal tooltip */}
        {hoveredTerm && (()=>{
          const flipLeft = mousePos.x > (svgRef.current?.getBoundingClientRect().width || MAP_W) * 0.65;
          const tipW = 210;
          const served = STORES.filter(s=>s.terminal===hoveredTerm.id).length;
          return (
            <div style={{
              position:"absolute",
              left: flipLeft ? mousePos.x - tipW - 14 : mousePos.x + 14,
              top:  mousePos.y - 10,
              width:tipW,zIndex:20,pointerEvents:"none",
              background:darkMode?"rgba(11,14,22,.95)":"rgba(255,255,255,.98)",
              border:`1px solid #F4D398`,
              borderRadius:8,boxShadow:"0 8px 24px rgba(0,0,0,.28)",
              backdropFilter:"blur(12px)",WebkitBackdropFilter:"blur(12px)",
              fontFamily:FONT,overflow:"hidden",
            }}>
              <div style={{padding:"8px 12px",background:darkMode?"rgba(200,164,74,.08)":"rgba(200,164,74,.07)",
                borderBottom:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`}}>
                <div style={{fontSize:9,fontWeight:800,letterSpacing:.6,color:"#F4D398",textTransform:"uppercase"}}>Terminal</div>
                <div style={{fontSize:11.5,fontWeight:700,color:C.textPri,marginTop:1}}>{hoveredTerm.name}</div>
              </div>
              <div style={{padding:"8px 12px",display:"grid",gridTemplateColumns:"1fr 1fr",gap:6,fontSize:10}}>
                <div><div style={{color:C.textMut,fontSize:9}}>Pipeline</div><div style={{color:C.textSec,fontWeight:600,marginTop:1}}>{hoveredTerm.pipeline}</div></div>
                <div><div style={{color:C.textMut,fontSize:9}}>Supplier</div><div style={{color:C.textSec,fontWeight:600,marginTop:1}}>{hoveredTerm.supplier}</div></div>
                <div><div style={{color:C.textMut,fontSize:9}}>Code</div><div style={{color:C.textSec,fontWeight:600,marginTop:1,fontFamily:"Arial,sans-serif"}}>{hoveredTerm.short}</div></div>
                <div><div style={{color:C.textMut,fontSize:9}}>Stores served</div><div style={{color:C.textSec,fontWeight:600,marginTop:1,fontFamily:"Arial,sans-serif"}}>{served}</div></div>
              </div>
            </div>
          );
        })()}
      </div>
    </div>
  );
}


// ── ReplenMapPage — Full-page Replen. Map tab, d3 Mercator + TopoJSON ───────
// A larger, interactive version of ReplenMap used on the dedicated "Replen.
// Map" tab. Keeps all existing features (filters, truck routes, pulse rings,
// side panel, dispatch button) but uses the same real-state-boundary basemap
// as the RD Profitability Suite.
const REPLEN_MAP_W = 940, REPLEN_MAP_H = 640;
function ReplenMapPage({
  darkMode, C, FONT,
  mapFilter, setMapFilter,
  mapGrade, setMapGrade,
  hoveredStore, setHoveredStore,
  selectedStore, setSelectedStore,
  liveLoads,
  onDispatch,
}) {
  const svgRef = useRef(null);
  const [features, setFeatures]   = useState([]);
  const [proj, setProj]           = useState(null);
  const [pathGen, setPathGen]     = useState(null);
  const [mapStatus, setMapStatus] = useState("loading");
  const [zoomT, setZoomT]         = useState({x:0,y:0,k:1});
  const [mousePos, setMousePos]   = useState({x:0,y:0});
  const [showRoutes, setShowRoutes] = useState(true);
  const [showLabels, setShowLabels] = useState(true);
  const [showTerritories, setShowTerritories] = useState(false);

  // ─── Service-territory color map ─────────────────────────────────────────────
  // One color per terminal — derived from zone color at module level (TERMINAL_COLORS)

  // Load TopoJSON once
  useEffect(()=>{
    const URLS = [
      "https://cdn.jsdelivr.net/npm/us-atlas@3/states-10m.json",
      "https://unpkg.com/us-atlas@3/states-10m.json",
    ];
    let cancelled = false;
    (async()=>{
      for (const url of URLS) {
        try {
          const res = await fetch(url); if (!res.ok) continue;
          const topo = await res.json();
          if (cancelled) return;
          const all = topoFeatures(topo, "states");
          const filtered = all.filter(f=>SE_SHOW_FIPS.has(String(f.id).padStart(2,"0")));
          const fc = { type:"FeatureCollection", features:filtered };
          const p  = d3.geoMercator().fitExtent([[14,14],[REPLEN_MAP_W-14,REPLEN_MAP_H-14]], fc);
          const pg = d3.geoPath().projection(p);
          setFeatures(filtered); setProj(()=>p); setPathGen(()=>pg); setMapStatus("ok");
          return;
        } catch (e) { console.warn("ReplenMapPage topology load failed:", url, e.message); }
      }
      if (!cancelled) setMapStatus("error");
    })();
    return ()=>{ cancelled = true; };
  }, []);

  // Wire up d3.zoom
  useEffect(()=>{
    if (!svgRef.current || mapStatus!=="ok") return;
    const zoom = d3.zoom().scaleExtent([0.8, 12]).on("zoom", (event)=>{
      const { x, y, k } = event.transform;
      setZoomT({ x, y, k });
    });
    d3.select(svgRef.current).call(zoom);
    svgRef.current.__zoom_instance = zoom;
    return ()=>{ if (svgRef.current) d3.select(svgRef.current).on(".zoom", null); };
  }, [mapStatus]);

  const doZoom = (factor) => {
    if (!svgRef.current || !svgRef.current.__zoom_instance) return;
    d3.select(svgRef.current).transition().duration(250)
      .call(svgRef.current.__zoom_instance.scaleBy, factor);
  };
  const resetZoom = () => {
    if (!svgRef.current || !svgRef.current.__zoom_instance) return;
    d3.select(svgRef.current).transition().duration(350)
      .call(svgRef.current.__zoom_instance.transform, d3.zoomIdentity);
  };
  const onSvgMouseMove = (e) => {
    if (!svgRef.current) return;
    const rect = svgRef.current.getBoundingClientRect();
    setMousePos({ x: e.clientX - rect.left, y: e.clientY - rect.top });
  };

  // Build store data with status + inbound lookup
  const storeData = useMemo(()=>STORES.map(s=>{
    const dep = DEPLETION.find(d=>d.storeId===s.id);
    // Status matches the Inventory tab's thresholds so both views agree:
    //   CRITICAL: any grade <1 day supply (matches Inventory's critical count)
    //   URGENT:   any grade <1.5 days supply
    //   REORDER:  any grade <2 days supply (matches Inventory's reorder count)
    //   OK:       all grades >=2 days supply
    const status = dep?.minReorder < 1    ? "CRITICAL"
                 : dep?.minReorder < 1.5  ? "URGENT"
                 : dep?.minReorder < 2    ? "REORDER"
                 : "OK";
    const col = {CRITICAL:"#EF4444",URGENT:"#FBBF24",REORDER:"#F4D398",OK:"#22C55E"}[status];
    const inbound = liveLoads.find(l=>l.dest===s.name&&["SCHEDULED","LOADING","EN ROUTE","DELIVERING"].includes(l.status));
    return {...s, dep, status, col, inbound};
  }), [liveLoads]);

  const filtered = useMemo(()=>storeData.filter(s=>{
    if (mapFilter!=="ALL" && s.status!==mapFilter) return false;
    if (mapGrade!=="ALL") {
      const dep = s.dep;
      if (!dep) return false;
      const daysLeft = dep.forecast[mapGrade]?.daysToReorder||99;
      if (mapFilter==="ALL" && daysLeft>3) return false;
    }
    return true;
  }), [storeData, mapFilter, mapGrade]);

  // Basemap palette — mirrors RD
  const bgFill         = darkMode ? "#0D1421" : "#E8EAED";
  const stateFillMkt   = darkMode ? "#1A2B45" : "#FFFFFF";
  const stateFillOther = darkMode ? "#111D2E" : "#D4D8DE";
  const stateStroke    = darkMode ? "#253650" : "#B4BAC2";
  const labelColMkt    = darkMode ? "#4A7AA0" : "#8A96A4";
  const labelColOther  = darkMode ? "#253650" : "#A8AEB6";

  const sel = selectedStore || hoveredStore;

  return (
    <div style={{display:"flex",flexDirection:"column",gap:12}}>

      {/* Controls bar */}
      <div style={{display:"flex",alignItems:"center",gap:10,flexWrap:"wrap"}}>
        <div style={{display:"flex",gap:5}}>
          {[{f:"ALL",l:"All Stores",c:C.textSec},{f:"CRITICAL",l:"Critical",c:"#EF4444"},{f:"URGENT",l:"Urgent",c:"#FBBF24"},{f:"REORDER",l:"Reorder",c:"#F4D398"},{f:"OK",l:"On Plan",c:"#22C55E"}].map(btn=>(
            <button key={btn.f} onClick={()=>setMapFilter(btn.f)}
              style={{padding:"5px 12px",borderRadius:6,border:`1.5px solid ${mapFilter===btn.f?btn.c:C.cardBord}`,background:mapFilter===btn.f?`${btn.c}18`:"transparent",color:mapFilter===btn.f?btn.c:C.textSec,fontSize:10.5,fontWeight:mapFilter===btn.f?700:400,cursor:"pointer",fontFamily:FONT}}>
              {btn.l}
            </button>
          ))}
        </div>
        <div style={{width:1,height:22,background:C.cardBord}}/>
        {["ALL",...GRADES].map(g=>(
          <button key={g} onClick={()=>setMapGrade(g)}
            style={{padding:"4px 10px",borderRadius:6,border:`1px solid ${mapGrade===g?C.blue:C.cardBord}`,background:mapGrade===g?(darkMode?"rgba(59,130,246,.12)":"#EFF6FF"):"transparent",color:mapGrade===g?C.blue:C.textSec,fontSize:10.5,fontWeight:mapGrade===g?700:400,cursor:"pointer",fontFamily:FONT}}>
            {g==="ALL"?"All Grades":g}
          </button>
        ))}
        <div style={{width:1,height:22,background:C.cardBord}}/>
        {/* Layer toggles */}
        <button onClick={()=>setShowRoutes(!showRoutes)}
          style={{padding:"4px 10px",borderRadius:6,border:`1px solid ${showRoutes?C.gold:C.cardBord}`,background:showRoutes?(darkMode?"rgba(200,164,74,.12)":"#FFFDF0"):"transparent",color:showRoutes?C.gold:C.textSec,fontSize:10.5,fontWeight:showRoutes?700:400,cursor:"pointer",fontFamily:FONT}}>
          Pipelines {showRoutes?"•":"○"}
        </button>
        <button onClick={()=>setShowLabels(!showLabels)}
          style={{padding:"4px 10px",borderRadius:6,border:`1px solid ${showLabels?C.gold:C.cardBord}`,background:showLabels?(darkMode?"rgba(200,164,74,.12)":"#FFFDF0"):"transparent",color:showLabels?C.gold:C.textSec,fontSize:10.5,fontWeight:showLabels?700:400,cursor:"pointer",fontFamily:FONT}}>
          Labels {showLabels?"•":"○"}
        </button>
        <button onClick={()=>setShowTerritories(!showTerritories)}
          style={{padding:"4px 10px",borderRadius:6,border:`1px solid ${showTerritories?C.gold:C.cardBord}`,background:showTerritories?(darkMode?"rgba(200,164,74,.12)":"#FFFDF0"):"transparent",color:showTerritories?C.gold:C.textSec,fontSize:10.5,fontWeight:showTerritories?700:400,cursor:"pointer",fontFamily:FONT}}>
          Territories {showTerritories?"•":"○"}
        </button>
        <div style={{marginLeft:"auto",display:"flex",gap:10,alignItems:"center",fontSize:10.5,color:C.textSec}}>
          <span>Showing {filtered.length} of {STORES.length} stores</span>
        </div>
      </div>

      {/* Main content */}
      <div style={{display:"flex",gap:14}}>

        {/* MAP */}
        <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden",position:"relative",minHeight:520}}>
          {/* Loading / error overlay */}
          {mapStatus!=="ok" && (
            <div style={{position:"absolute",inset:0,display:"flex",alignItems:"center",justifyContent:"center",
              color:C.textSec,fontSize:13,fontFamily:FONT,zIndex:5,background:bgFill}}>
              {mapStatus==="loading" ? "Loading basemap…" : "Map unavailable — check network"}
            </div>
          )}

          <svg ref={svgRef} width="100%"
            viewBox={`0 0 ${REPLEN_MAP_W} ${REPLEN_MAP_H}`}
            preserveAspectRatio="xMidYMid meet"
            onMouseMove={onSvgMouseMove}
            style={{display:"block",cursor:"grab",background:bgFill}}>
            <defs>
              <filter id="rmp_dshadow" x="-40%" y="-40%" width="180%" height="180%">
                <feDropShadow dx="0" dy="2" stdDeviation="2.5" floodColor="#000" floodOpacity="0.22"/>
              </filter>
              <filter id="rmp_glow" x="-100%" y="-100%" width="300%" height="300%">
                <feGaussianBlur stdDeviation="3" result="b"/>
                <feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge>
              </filter>
              <marker id="rmp_arrow_gold" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto">
                <path d="M0,0 L0,7 L7,3.5 Z" fill="#F4D398" fillOpacity="0.9"/>
              </marker>
              <marker id="rmp_arrow_blue" markerWidth="7" markerHeight="7" refX="6" refY="3.5" orient="auto">
                <path d="M0,0 L0,7 L7,3.5 Z" fill="#3B82F6" fillOpacity="0.9"/>
              </marker>
            </defs>

            {/* Flat basemap */}
            <rect width={REPLEN_MAP_W} height={REPLEN_MAP_H} fill={bgFill}/>

            {/* Zoom + pan transform group */}
            <g transform={`translate(${zoomT.x},${zoomT.y}) scale(${zoomT.k})`}>

              {/* State fills */}
              {pathGen && features.map((ft,i)=>{
                const fips = String(ft.id).padStart(2,"0");
                const isMkt = SE_MARKET_FIPS.has(fips);
                return (
                  <path key={i} d={pathGen(ft)||""}
                    fill={isMkt?stateFillMkt:stateFillOther}
                    stroke={stateStroke} strokeWidth={0.8/zoomT.k}/>
                );
              })}

              {/* State labels */}
              {pathGen && features.map((ft,i)=>{
                const fips = String(ft.id).padStart(2,"0");
                const abbr = SE_FIPS_ABBR[fips]; if (!abbr) return null;
                const c = pathGen.centroid(ft); if (!c || isNaN(c[0])) return null;
                const isMkt = SE_MARKET_FIPS.has(fips);
                return (
                  <text key={`l${i}`} x={c[0]} y={c[1]+1} textAnchor="middle"
                    fill={isMkt?labelColMkt:labelColOther}
                    fontSize={11/Math.sqrt(zoomT.k)} fontWeight={700} letterSpacing={1.4}
                    style={{pointerEvents:"none",userSelect:"none",fontFamily:"Arial,sans-serif"}}>
                    {abbr}
                  </text>
                );
              })}

              {/* ── Service Territories — Voronoi cells colored by assigned terminal ── */}
              {/* Each store already has a .terminal field; we compute one Voronoi     */}
              {/* cell per store in projected pixel space, then color the cell by its  */}
              {/* terminal assignment. Adjacent cells with the same color merge        */}
              {/* visually into a service territory. The whole layer is clipped to the */}
              {/* union of market-state outlines so zones don't bleed into ocean/inland*/}
              {/* transit states.                                                      */}
              {showTerritories && proj && pathGen && features.length>0 && (()=>{
                // Project all stores to pixel space; keep the store reference alongside
                const projected = STORES.map(s=>{
                  const p = proj([s.lng, s.lat]);
                  return (p && !isNaN(p[0])) ? { x:p[0], y:p[1], store:s } : null;
                }).filter(Boolean);

                if (projected.length < 3) return null;

                // d3-delaunay (bundled in d3 v7). Voronoi bounds a bit larger than
                // the viewport so edge cells don't get clipped prematurely before
                // the state-outline clip path takes over.
                const pts = projected.map(p=>[p.x, p.y]);
                const pad = 60;
                const delaunay = d3.Delaunay.from(pts);
                const voronoi = delaunay.voronoi([-pad, -pad, REPLEN_MAP_W+pad, REPLEN_MAP_H+pad]);

                // Build a clipPath from the union of market-state paths. Territory
                // cells only render within states where we actually have stores.
                const clipId = "territory-clip-rmp";
                const marketFeatures = features.filter(ft=>SE_MARKET_FIPS.has(String(ft.id).padStart(2,"0")));

                // Pick territory stroke based on theme so boundaries stay legible
                const cellStrokeOpacity = darkMode ? 0.6 : 0.55;

                // Count stores per terminal for the label badge
                const countsByTerm = {};
                projected.forEach(p=>{
                  const t = p.store.terminal;
                  countsByTerm[t] = (countsByTerm[t]||0) + 1;
                });

                return (
                  <g style={{pointerEvents:"none"}}>
                    <defs>
                      <clipPath id={clipId}>
                        {marketFeatures.map((ft,i)=>(
                          <path key={`cp${i}`} d={pathGen(ft)||""}/>
                        ))}
                      </clipPath>
                    </defs>
                    {/* Voronoi cells (the zones) */}
                    <g clipPath={`url(#${clipId})`}>
                      {projected.map((p,i)=>{
                        const cell = voronoi.cellPolygon(i);
                        if (!cell || cell.length<3) return null;
                        const color = TERMINAL_COLORS[p.store.terminal] || "#888";
                        const d = "M" + cell.map(pt=>`${pt[0].toFixed(1)},${pt[1].toFixed(1)}`).join("L") + "Z";
                        return (
                          <path key={`tc${i}`} d={d}
                            fill={color} fillOpacity={darkMode?0.22:0.18}
                            stroke={color} strokeOpacity={cellStrokeOpacity}
                            strokeWidth={0.6/zoomT.k} strokeLinejoin="round"/>
                        );
                      })}
                    </g>
                    {/* Territory badge above each terminal — "Z1 · SEL · 14" */}
                    {TERMINALS.map(t=>{
                      const p = proj([t.lng, t.lat]);
                      if (!p || isNaN(p[0])) return null;
                      const count = countsByTerm[t.id] || 0;
                      if (count===0) return null;
                      const color = TERMINAL_COLORS[t.id] || "#888";
                      const zone = TERMINAL_ZONE[t.id];
                      const label = `Z${zone?.id||"?"} · ${t.short} · ${count}`;
                      const scale = 1/Math.sqrt(zoomT.k);
                      return (
                        <g key={`tb${t.id}`} transform={`translate(${p[0].toFixed(1)},${(p[1]-28).toFixed(1)}) scale(${scale})`}>
                          <rect x={-label.length*3.4} y={-9} width={label.length*6.8} height={16}
                            rx={8} fill={color} fillOpacity={0.92}
                            stroke={darkMode?"#0D1421":"#fff"} strokeWidth={1.2}/>
                          <text x={0} y={2.5} textAnchor="middle"
                            fontSize={10} fontWeight={800} fill="#fff"
                            fontFamily="Arial,sans-serif"
                            style={{letterSpacing:.4,userSelect:"none"}}>
                            {label}
                          </text>
                        </g>
                      );
                    })}
                  </g>
                );
              })()}

              {/* Pipeline routes — real waypoints, only if toggled on */}
              {showRoutes && proj && (()=>{
                const routes = [
                  { pts:COLONIAL_ROUTE,   color:"#F4D398", label:"Colonial"   },
                  { pts:PLANTATION_ROUTE, color:"#3B82F6", label:"Plantation" },
                ];
                return routes.map((r,i)=>{
                  const poly = r.pts.map(([lng,lat])=>{
                    const p = proj([lng,lat]); return p?`${p[0].toFixed(1)},${p[1].toFixed(1)}`:null;
                  }).filter(Boolean).join(" ");
                  if (!poly) return null;
                  return (
                    <g key={`rt${i}`}>
                      {/* Casing */}
                      <polyline points={poly} fill="none" stroke={darkMode?"#000":"#fff"}
                        strokeWidth={3.4/zoomT.k} strokeOpacity={0.28}
                        strokeLinecap="round" strokeLinejoin="round"/>
                      {/* Main line with animated flow */}
                      <polyline points={poly} fill="none" stroke={r.color}
                        strokeWidth={1.8/zoomT.k} strokeOpacity={0.88}
                        strokeLinecap="round" strokeLinejoin="round"
                        strokeDasharray={`${8/zoomT.k},${5/zoomT.k}`}>
                        <animate attributeName="stroke-dashoffset" from="0" to={`-${26/zoomT.k}`} dur="2.4s" repeatCount="indefinite"/>
                      </polyline>
                    </g>
                  );
                });
              })()}

              {/* In-transit load routes + moving truck dots */}
              {proj && liveLoads.filter(l=>l.status==="EN ROUTE"||l.status==="DELIVERING").map(ld=>{
                const destStore = storeData.find(s=>s.name===ld.dest);
                const origTerm  = TERMINALS.find(t=>ld.origin.includes(t.name.split(",")[0]));
                if (!destStore || !origTerm) return null;
                const p1 = proj([origTerm.lng, origTerm.lat]);
                const p2 = proj([destStore.lng, destStore.lat]);
                if (!p1 || !p2 || isNaN(p1[0]) || isNaN(p2[0])) return null;
                const pct = ld.pct/100;
                const cx = p1[0] + (p2[0]-p1[0])*pct;
                const cy = p1[1] + (p2[1]-p1[1])*pct;
                const ldColor = ld.status==="DELIVERING"?"#22C55E":"#0891B2";
                return (
                  <g key={ld.id}>
                    <line x1={p1[0]} y1={p1[1]} x2={p2[0]} y2={p2[1]}
                      stroke={ldColor} strokeWidth={1.5/zoomT.k}
                      strokeDasharray={`${4/zoomT.k},${3/zoomT.k}`} opacity={0.6}/>
                    {/* Truck pulse */}
                    <circle cx={cx} cy={cy} r={9/zoomT.k} fill={ldColor} fillOpacity={0.22}>
                      <animate attributeName="r" values={`${7/zoomT.k};${12/zoomT.k};${7/zoomT.k}`} dur="2s" repeatCount="indefinite"/>
                    </circle>
                    <circle cx={cx} cy={cy} r={5/zoomT.k} fill={ldColor}
                      stroke={darkMode?"#0D1421":"#fff"} strokeWidth={1.5/zoomT.k}/>
                  </g>
                );
              })}

              {/* Store pins — dimmed first, then highlighted */}
              {proj && [...storeData.filter(s=>s.status==="OK"), ...storeData.filter(s=>s.status!=="OK")].map(s=>{
                const p = proj([s.lng, s.lat]); if (!p || isNaN(p[0])) return null;
                const x = p[0], y = p[1];
                const isSelected = selectedStore?.id===s.id;
                const isHovered  = hoveredStore?.id===s.id;
                const isFilt     = filtered.find(f=>f.id===s.id);
                const opacity    = isFilt ? 1 : 0.18;
                const r          = (isSelected?9:isHovered?8:s.status==="OK"?4:6.5)/Math.sqrt(zoomT.k);
                const hasInbound = !!s.inbound;
                return (
                  <g key={s.id} transform={`translate(${x.toFixed(1)},${y.toFixed(1)})`}
                    style={{cursor:"pointer"}}
                    onClick={()=>setSelectedStore(selectedStore?.id===s.id?null:s)}
                    onMouseEnter={()=>setHoveredStore(s)}
                    onMouseLeave={()=>setHoveredStore(null)}>
                    {/* Pulsing ring for critical/urgent */}
                    {(s.status==="CRITICAL"||s.status==="URGENT")&&isFilt&&(
                      <circle r={r+4} fill="none" stroke={s.col} strokeWidth={1.4/zoomT.k} strokeOpacity={0.7}>
                        <animate attributeName="r" values={`${r+2};${r+9};${r+2}`} dur="1.8s" repeatCount="indefinite"/>
                        <animate attributeName="stroke-opacity" values="0.7;0;0.7" dur="1.8s" repeatCount="indefinite"/>
                      </circle>
                    )}
                    {/* Inbound truck indicator (dashed green ring) */}
                    {hasInbound && (
                      <circle r={r+7} fill="none" stroke="#22C55E" strokeWidth={1.4/zoomT.k}
                        strokeDasharray={`${3/zoomT.k},${3/zoomT.k}`} strokeOpacity={0.75}/>
                    )}
                    {/* Selection / hover ring */}
                    {(isSelected||isHovered) && (
                      <circle r={r+3} fill="none" stroke={s.col}
                        strokeWidth={(isSelected?2:1.2)/zoomT.k}
                        strokeOpacity={isSelected?0.9:0.5}
                        strokeDasharray={isSelected?`${4/zoomT.k},${3/zoomT.k}`:"none"}/>
                    )}
                    {/* White halo + pin */}
                    <circle r={r+1.2/zoomT.k} fill={darkMode?"#0D1421":"#fff"} opacity={opacity}/>
                    <circle r={r} fill={s.col} opacity={opacity}
                      stroke={darkMode?"rgba(255,255,255,.45)":"rgba(13,22,40,.25)"}
                      strokeWidth={1.2/zoomT.k}
                      filter={(s.status==="CRITICAL"&&isFilt)?"url(#rmp_glow)":undefined}/>
                    {/* Label for critical/urgent */}
                    {showLabels && (s.status==="CRITICAL"||s.status==="URGENT") && isFilt && (
                      <text y={-(r+5)} textAnchor="middle"
                        fontSize={8.5/Math.sqrt(zoomT.k)} fontWeight={700}
                        fill={s.col} fontFamily="Arial,sans-serif" opacity={opacity}
                        style={{pointerEvents:"none",userSelect:"none"}}>
                        {s.name.length>18?s.name.substring(0,16)+"…":s.name}
                      </text>
                    )}
                  </g>
                );
              })}

              {/* Terminals — gold diamonds on top */}
              {proj && TERMINALS.map(t=>{
                const p = proj([t.lng, t.lat]); if (!p || isNaN(p[0])) return null;
                const ts = TERMINAL_STATUS[t.id];
                const congColor = ts?.congestion==="HIGH"?"#EF4444"
                  : ts?.congestion==="MODERATE"?"#FBBF24":"#22C55E";
                return (
                  <g key={t.id} transform={`translate(${p[0].toFixed(1)},${p[1].toFixed(1)})`}>
                    {/* Congestion outer ring */}
                    <circle r={14/Math.sqrt(zoomT.k)} fill={darkMode?"#0D1421":"#fff"}
                      stroke={congColor} strokeWidth={2.2/zoomT.k}
                      filter="url(#rmp_dshadow)"/>
                    {/* Inner gold diamond */}
                    <rect x={-5} y={-5} width={10} height={10} fill="#F4D398"
                      transform="rotate(45)"/>
                    <text y={24/Math.sqrt(zoomT.k)} textAnchor="middle"
                      fontSize={10/Math.sqrt(zoomT.k)}
                      fill={darkMode?"#F4D398":"#8B6914"}
                      fontFamily="Arial,sans-serif" fontWeight={800}
                      style={{pointerEvents:"none",userSelect:"none",letterSpacing:.5}}>
                      {t.short}
                    </text>
                  </g>
                );
              })}
            </g>
          </svg>

          {/* Glassmorphic legend — bottom-left */}
          {mapStatus==="ok" && (
            <div style={{position:"absolute",bottom:12,left:12,zIndex:10,
              padding:"8px 12px",borderRadius:10,
              background:darkMode?"rgba(13,22,39,.85)":"rgba(255,255,255,.90)",
              border:`1px solid ${darkMode?"#1E3A5A":"#CBD5E1"}`,
              boxShadow:"0 2px 10px rgba(0,0,0,.22)",
              backdropFilter:"blur(10px)",WebkitBackdropFilter:"blur(10px)",
              fontFamily:FONT,
            }}>
              <div style={{fontSize:9,fontWeight:800,color:darkMode?"#7B9EBE":C.textSec,
                letterSpacing:.6,textTransform:"uppercase",marginBottom:6}}>
                Store Status
              </div>
              {[
                {c:"#EF4444",l:"Critical"},
                {c:"#FBBF24",l:"Urgent"},
                {c:"#F4D398",l:"Reorder"},
                {c:"#22C55E",l:"On Plan"},
              ].map((item,i)=>(
                <div key={i} style={{display:"flex",alignItems:"center",gap:6,marginBottom:3}}>
                  <div style={{width:8,height:8,borderRadius:"50%",background:item.c,
                    boxShadow:item.c==="#EF4444"?`0 0 6px ${item.c}99`:"none"}}/>
                  <span style={{fontSize:10,color:darkMode?"#B7C7DC":C.textSec}}>{item.l}</span>
                </div>
              ))}
              <div style={{height:1,background:darkMode?"#1E3A5A":"#E5E9EF",margin:"6px 0"}}/>
              <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:3}}>
                <div style={{width:18,height:2,background:"#F4D398"}}/>
                <span style={{fontSize:10,color:darkMode?"#B7C7DC":C.textSec}}>Colonial</span>
              </div>
              <div style={{display:"flex",alignItems:"center",gap:6}}>
                <div style={{width:18,height:2,background:"#3B82F6"}}/>
                <span style={{fontSize:10,color:darkMode?"#B7C7DC":C.textSec}}>Plantation</span>
              </div>
              {/* Territory legend — only when territories layer is on */}
              {showTerritories && (
                <>
                  <div style={{height:1,background:darkMode?"#1E3A5A":"#E5E9EF",margin:"6px 0"}}/>
                  <div style={{fontSize:9,fontWeight:800,color:darkMode?"#7B9EBE":C.textSec,
                    letterSpacing:.6,textTransform:"uppercase",marginBottom:5}}>
                    Terminal Territory
                  </div>
                  {TERMINALS.map(t=>(
                    <div key={t.id} style={{display:"flex",alignItems:"center",gap:6,marginBottom:2.5}}>
                      <div style={{width:10,height:10,borderRadius:2,
                        background:TERMINAL_COLORS[t.id]||"#888",opacity:0.85,
                        border:`1px solid ${TERMINAL_COLORS[t.id]||"#888"}`}}/>
                      <span style={{fontSize:10,color:darkMode?"#B7C7DC":C.textSec,fontFamily:"Arial,sans-serif"}}>
                        <span style={{fontWeight:700}}>{t.short}</span>
                        <span style={{opacity:.7,marginLeft:4}}>· {t.name.split(",")[0]}</span>
                      </span>
                    </div>
                  ))}
                </>
              )}
            </div>
          )}

          {/* Glassmorphic counts chip — top-left */}
          {mapStatus==="ok" && (
            <div style={{
              position:"absolute",top:12,left:12,zIndex:10,
              display:"flex",alignItems:"center",gap:12,
              padding:"8px 14px",borderRadius:22,
              background:darkMode?"rgba(13,22,39,.85)":"rgba(255,255,255,.90)",
              border:`1px solid ${darkMode?"#1E3A5A":"#CBD5E1"}`,
              boxShadow:"0 2px 10px rgba(0,0,0,.22)",
              backdropFilter:"blur(10px)",WebkitBackdropFilter:"blur(10px)",
            }}>
              {[
                { n:storeData.filter(s=>s.status==="CRITICAL").length, c:"#EF4444", l:"critical" },
                { n:storeData.filter(s=>s.status==="URGENT").length,   c:"#FBBF24", l:"urgent" },
                { n:storeData.filter(s=>s.status==="REORDER").length,  c:"#F4D398", l:"reorder" },
                { n:liveLoads.filter(l=>["EN ROUTE","DELIVERING"].includes(l.status)).length, c:"#0891B2", l:"en route" },
              ].map((s,i)=>(
                <div key={i} style={{display:"flex",alignItems:"center",gap:6,fontSize:11,fontWeight:600,color:darkMode?"#7B9EBE":C.textSec,fontFamily:FONT}}>
                  <span style={{
                    display:"inline-flex",alignItems:"center",justifyContent:"center",
                    minWidth:20,height:20,padding:"0 6px",borderRadius:10,
                    background:s.c,color:"#fff",fontSize:10.5,fontWeight:800,
                    fontFamily:"Arial,sans-serif",
                  }}>{s.n}</span>
                  {s.l}
                </div>
              ))}
            </div>
          )}

          {/* Zoom controls — bottom-right */}
          {mapStatus==="ok" && (
            <div style={{position:"absolute",bottom:12,right:12,display:"flex",flexDirection:"column",gap:3,zIndex:10}}>
              {[
                { label:"+", title:"Zoom in",  fn:()=>doZoom(1.5) },
                { label:"−", title:"Zoom out", fn:()=>doZoom(1/1.5) },
                { label:"⊙", title:"Reset",    fn:resetZoom },
              ].map(btn=>(
                <button key={btn.label} title={btn.title} onClick={btn.fn}
                  style={{
                    width:32,height:32,borderRadius:7,
                    border:`1px solid ${darkMode?"rgba(255,255,255,.1)":"rgba(255,255,255,.85)"}`,
                    background:darkMode?"rgba(4,14,26,.80)":"rgba(255,255,255,.82)",
                    backdropFilter:"blur(10px)",WebkitBackdropFilter:"blur(10px)",
                    color:darkMode?"#6A9DC0":C.textSec,
                    fontSize:18,fontWeight:700,cursor:"pointer",
                    display:"flex",alignItems:"center",justifyContent:"center",lineHeight:1,
                    boxShadow:"0 2px 8px rgba(0,0,0,.22)",fontFamily:"Arial,sans-serif",
                  }}>
                  {btn.label}
                </button>
              ))}
            </div>
          )}

          {/* Zone legend — bottom-left */}
          {mapStatus==="ok" && (
            <div style={{
              position:"absolute", bottom:12, left:12, zIndex:10,
              display:"flex", flexDirection:"column", gap:4,
              background: darkMode?"rgba(4,14,26,.82)":"rgba(255,255,255,.90)",
              border:`1px solid ${darkMode?"rgba(255,255,255,.08)":"rgba(0,0,0,.10)"}`,
              borderRadius:8, padding:"8px 10px",
              boxShadow:"0 2px 10px rgba(0,0,0,.22)",
              backdropFilter:"blur(10px)", WebkitBackdropFilter:"blur(10px)",
            }}>
              <div style={{fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:2}}>Zones</div>
              {ZONES.map(z => (
                <div key={z.id} style={{display:"flex", alignItems:"center", gap:6}}>
                  <span style={{
                    width:22, height:14, borderRadius:3,
                    background:z.color, display:"flex", alignItems:"center", justifyContent:"center",
                    fontSize:8, fontWeight:900, color:"#fff", fontFamily:"Arial,sans-serif", flexShrink:0,
                  }}>Z{z.id}</span>
                  <span style={{fontSize:9.5, color:C.textSec, fontFamily:FONT, whiteSpace:"nowrap"}}>{z.name}</span>
                </div>
              ))}
            </div>
          )}

          {/* Hover tooltip for stores (lightweight — only shown when no store is selected) */}
          {hoveredStore && !selectedStore && (()=>{
            const s = hoveredStore;
            const flipLeft = mousePos.x > (svgRef.current?.getBoundingClientRect().width || REPLEN_MAP_W) * 0.62;
            const tipW = 210;
            return (
              <div style={{
                position:"absolute",
                left: flipLeft ? mousePos.x - tipW - 14 : mousePos.x + 14,
                top:  mousePos.y - 10,
                width:tipW,zIndex:20,pointerEvents:"none",
                background:darkMode?"rgba(11,14,22,.95)":"rgba(255,255,255,.98)",
                border:`1px solid ${darkMode?"#1E3A5A":"#CBD5E1"}`,
                borderRadius:8,boxShadow:"0 8px 24px rgba(0,0,0,.28)",
                backdropFilter:"blur(12px)",WebkitBackdropFilter:"blur(12px)",
                fontFamily:FONT,overflow:"hidden",
              }}>
                <div style={{padding:"8px 12px",borderBottom:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`}}>
                  <div style={{fontSize:11.5,fontWeight:700,color:C.textPri,lineHeight:1.25}}>{s.name}</div>
                  <div style={{fontSize:10,color:C.textMut,marginTop:2,display:"flex",alignItems:"center",gap:5}}>
                    {s.city}, {s.state}
                    {(() => {
                      const zone = TERMINAL_ZONE[s.terminal];
                      return zone ? (
                        <span style={{fontSize:8,fontWeight:800,padding:"1px 5px",borderRadius:3,background:zone.color,color:"#fff",letterSpacing:.3}}>
                          Z{zone.id}
                        </span>
                      ) : null;
                    })()}
                  </div>
                </div>
                <div style={{padding:"8px 12px",display:"flex",alignItems:"center",justifyContent:"space-between",gap:8}}>
                  <span style={{fontSize:9.5,fontWeight:800,letterSpacing:.5,
                    color:"#fff",background:s.col,padding:"2px 7px",borderRadius:4,fontFamily:"Arial,sans-serif"}}>
                    {s.status}
                  </span>
                  {s.dep && (
                    <span style={{fontSize:10.5,color:C.textSec,fontWeight:600,fontFamily:"Arial,sans-serif"}}>
                      {s.dep.minCritical<=7 ? `${s.dep.minCritical.toFixed(1)}d to critical` : `${s.dep.minReorder.toFixed(1)}d to reorder`}
                    </span>
                  )}
                </div>
                {s.inbound && (
                  <div style={{padding:"6px 12px",borderTop:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`,
                    background:darkMode?"rgba(34,197,94,.08)":"#F0FDF4",
                    display:"flex",alignItems:"center",gap:6}}>
                    <div style={{width:6,height:6,borderRadius:"50%",background:"#22C55E"}}/>
                    <span style={{fontSize:10,color:"#16A34A",fontWeight:700}}>Inbound · {s.inbound.pct}% · ETA {s.inbound.eta}</span>
                  </div>
                )}
                <div style={{padding:"5px 12px",fontSize:9.5,color:C.textMut,
                  background:darkMode?"#0B0E16":"#FAFBFD",
                  borderTop:`1px solid ${darkMode?"#1E3A5A":"#E5E9EF"}`,textAlign:"center"}}>
                  Click pin to inspect
                </div>
              </div>
            );
          })()}
        </div>

        {/* SIDE PANEL */}
        <div style={{width:300,flexShrink:0,display:"flex",flexDirection:"column",gap:12}}>

          {/* Selected store detail */}
          {sel ? (
            <div style={{background:C.cardBg,border:`2px solid ${sel.col}`,borderRadius:10,padding:14}}>
              <div style={{display:"flex",justifyContent:"space-between",alignItems:"flex-start",marginBottom:10}}>
                <div style={{flex:1,minWidth:0}}>
                  <div style={{fontSize:12,fontWeight:800,color:C.textPri,fontFamily:FONT,marginBottom:3}}>{sel.name}</div>
                  <div style={{fontSize:10,color:C.textMut}}>{sel.city}, {sel.state} · {TERMINALS.find(t=>t.id===sel.terminal)?.short}</div>
                </div>
                <span style={{fontSize:9,fontWeight:800,padding:"3px 8px",borderRadius:5,background:`${sel.col}22`,color:sel.col,border:`1px solid ${sel.col}40`,flexShrink:0,marginLeft:8}}>
                  {sel.status}
                </span>
              </div>

              {/* Grade bars */}
              <div style={{display:"flex",flexDirection:"column",gap:7,marginBottom:12}}>
                {GRADES.map(g=>{
                  const pct = Math.min(1,(sel.invLevel[g]/(sel.tanks[g]||1)));
                  const dep = sel.dep?.forecast[g];
                  const gc = {Regular:"#0891B2",Premium:"#0D9488",Diesel:"#EA580C"}[g];
                  const dangerColor = pct<0.15?"#EF4444":pct<0.30?"#FBBF24":gc;
                  return (
                    <div key={g}>
                      <div style={{display:"flex",justifyContent:"space-between",marginBottom:3}}>
                        <span style={{fontSize:10.5,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{g}</span>
                        <div style={{display:"flex",gap:10}}>
                          <span style={{fontSize:10,color:C.textMut}}>{(sel.invLevel[g]/1000).toFixed(1)}K / {(sel.tanks[g]/1000).toFixed(0)}K gal</span>
                          <span style={{fontSize:10,fontWeight:700,color:dangerColor}}>{dep?.daysToReorder.toFixed(1)}d</span>
                        </div>
                      </div>
                      <div style={{height:7,background:C.cardBord,borderRadius:3,overflow:"hidden"}}>
                        <div style={{height:"100%",width:`${pct*100}%`,background:dangerColor,borderRadius:3}}/>
                      </div>
                    </div>
                  );
                })}
              </div>

              {/* Inbound load */}
              {sel.inbound ? (
                <div style={{padding:"8px 10px",borderRadius:7,background:darkMode?"rgba(34,197,94,.1)":"#F0FDF4",border:"1px solid rgba(34,197,94,.3)",marginBottom:10}}>
                  <div style={{fontSize:10,fontWeight:700,color:"#22C55E",marginBottom:2}}>Inbound Load</div>
                  <div style={{fontSize:10.5,color:C.textSec}}>{sel.inbound.id} · {sel.inbound.carrier} · {sel.inbound.driver}</div>
                  <div style={{fontSize:10,color:C.textSec}}>{sel.inbound.gals.toLocaleString()} gal {sel.inbound.grade} · ETA {sel.inbound.eta}</div>
                  <div style={{marginTop:5,height:4,background:C.cardBord,borderRadius:2,overflow:"hidden"}}>
                    <div style={{height:"100%",width:`${sel.inbound.pct}%`,background:"#22C55E",borderRadius:2}}/>
                  </div>
                </div>
              ) : sel.status!=="OK" ? (
                <div style={{padding:"8px 10px",borderRadius:7,background:darkMode?"rgba(239,68,68,.08)":"#FFF5F5",border:`1px solid ${sel.col}30`,marginBottom:10}}>
                  <div style={{fontSize:10,fontWeight:700,color:sel.col,marginBottom:2}}>No inbound load scheduled</div>
                  <div style={{fontSize:10,color:C.textSec}}>Dispatch needed · {CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(sel.terminal||""))?.short||"Check carrier availability"}</div>
                </div>
              ) : null}

              {/* Action buttons */}
              <div style={{display:"flex",gap:6}}>
                {sel.status!=="OK"&&!sel.inbound&&(
                  <button onClick={()=>{
                    const urgGrade = GRADES.find(g=>sel.dep?.forecast[g]?.daysToReorder<=3)||"Regular";
                    const vol = Math.round((sel.tanks?.[urgGrade]||8000)*0.78/500)*500;
                    const avail = CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(sel.terminal||""));
                    onDispatch({storeId:sel.id,grade:urgGrade,vol,storeName:sel.name,terminal:sel.terminal,carrierId:avail?.id||null});
                  }} style={{flex:1,padding:"7px 0",borderRadius:7,border:"none",background:sel.col,color:"#fff",fontSize:11,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                    Dispatch
                  </button>
                )}
                <button onClick={()=>setSelectedStore(null)}
                  style={{padding:"7px 12px",borderRadius:7,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:11,cursor:"pointer",fontFamily:FONT}}>
                  Clear
                </button>
              </div>
            </div>
          ) : (
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:14}}>
              <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:8}}>Click a store to inspect</div>
              <div style={{fontSize:10.5,color:C.textSec,lineHeight:1.5}}>
                Pins are color-coded by inventory status. Pulsing rings = critical or urgent. Dashed green ring = inbound truck en route. Moving dots on routes = active loads. Scroll to zoom, drag to pan.
              </div>
            </div>
          )}

          {/* Portfolio status */}
          <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:14}}>
            <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:10}}>Portfolio Status</div>
            {[
              {l:"Critical",   n:storeData.filter(s=>s.status==="CRITICAL").length, c:"#EF4444"},
              {l:"Urgent",     n:storeData.filter(s=>s.status==="URGENT").length,   c:"#FBBF24"},
              {l:"Reorder",    n:storeData.filter(s=>s.status==="REORDER").length,  c:"#F4D398"},
              {l:"On Plan",    n:storeData.filter(s=>s.status==="OK").length,        c:"#22C55E"},
              {l:"With Inbound",n:storeData.filter(s=>s.inbound).length,            c:"#0891B2"},
            ].map((row,i)=>(
              <div key={i} style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"5px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                <div style={{display:"flex",alignItems:"center",gap:7}}>
                  <div style={{width:9,height:9,borderRadius:"50%",background:row.c}}/>
                  <span style={{fontSize:10.5,color:C.textSec,fontFamily:FONT}}>{row.l}</span>
                </div>
                <div style={{display:"flex",alignItems:"center",gap:8}}>
                  <div style={{width:80,height:5,background:C.cardBord,borderRadius:2,overflow:"hidden"}}>
                    <div style={{height:"100%",width:`${(row.n/STORES.length)*100}%`,background:row.c,borderRadius:2}}/>
                  </div>
                  <span style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,width:20,textAlign:"right"}}>{row.n}</span>
                </div>
              </div>
            ))}
          </div>

          {/* Active loads */}
          <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:14}}>
            <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:10}}>
              Active Loads — {liveLoads.filter(l=>["EN ROUTE","DELIVERING"].includes(l.status)).length} en route
            </div>
            {liveLoads.filter(l=>["EN ROUTE","DELIVERING"].includes(l.status)).map(ld=>(
              <div key={ld.id} style={{padding:"7px 0",borderBottom:`1px solid ${C.cardBord}`,display:"flex",gap:8,alignItems:"center"}}>
                <div style={{width:7,height:7,borderRadius:"50%",background:ld.status==="DELIVERING"?"#22C55E":"#0891B2",flexShrink:0}}/>
                <div style={{flex:1,minWidth:0}}>
                  <div style={{fontSize:10.5,fontWeight:600,color:C.textPri,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{ld.id} → {ld.dest}</div>
                  <div style={{fontSize:9.5,color:C.textMut}}>{ld.driver} · {ld.gals.toLocaleString()} gal · {ld.pct}%</div>
                </div>
                <span style={{fontSize:9.5,fontWeight:700,color:ld.status==="DELIVERING"?"#22C55E":"#0891B2",flexShrink:0}}>{ld.eta}</span>
              </div>
            ))}
            {liveLoads.filter(l=>["EN ROUTE","DELIVERING"].includes(l.status)).length===0&&(
              <div style={{fontSize:10.5,color:C.textMut,textAlign:"center",padding:"8px 0"}}>No active routes</div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
}


// ─── PageHeader — consistent title + subtitle at the top of every tab ───────
// Gives each page a single clear "this is what this page is for" banner. Also
// optionally shows a crumb (e.g., "From · Critical alert for Store #7") when
// the user navigated here from somewhere contextual, so they always know how
// they got to the screen they're on.
function PageHeader({ title, subtitle, crumb, onClearCrumb, C, darkMode, right }) {
  const FONT = "Arial,sans-serif";
  return (
    <div style={{ marginBottom:14 }}>
      {crumb && (
        <div style={{
          display:"inline-flex", alignItems:"center", gap:8,
          padding:"4px 10px", borderRadius:14, marginBottom:8,
          background: darkMode ? "rgba(200,164,74,.12)" : "#FFF9E6",
          border: `1px solid ${darkMode ? "rgba(200,164,74,.35)" : "#F1D98F"}`,
          fontSize:10.5, color: darkMode ? "#F4D398" : "#8B6914",
          fontFamily: FONT,
        }}>
          <span style={{ fontSize:9, fontWeight:800, letterSpacing:.6, textTransform:"uppercase", opacity:.8 }}>From</span>
          <span style={{ fontWeight:600 }}>{crumb}</span>
          {onClearCrumb && (
            <button onClick={onClearCrumb} aria-label="clear"
              style={{
                marginLeft:4, border:"none", background:"transparent",
                color: darkMode ? "#F4D398" : "#8B6914",
                cursor:"pointer", fontSize:12, lineHeight:1, padding:0,
              }}>×</button>
          )}
        </div>
      )}
      <div style={{ display:"flex", alignItems:"flex-end", justifyContent:"space-between", gap:12 }}>
        <div style={{ minWidth:0 }}>
          <div style={{
            fontSize:20, fontWeight:800, color:C.textPri, fontFamily:FONT,
            letterSpacing:.2, lineHeight:1.15,
          }}>{title}</div>
          {subtitle && (
            <div style={{
              fontSize:12, color:C.textSec, marginTop:3, fontFamily:FONT,
              letterSpacing:.1, lineHeight:1.3,
            }}>{subtitle}</div>
          )}
        </div>
        {right && <div style={{ flexShrink:0 }}>{right}</div>}
      </div>
    </div>
  );
}


// ─── DailyPlanOptimizer — greedy per-load landed-cost optimizer ─────────────
// Given: all stores, their current inventory vs tank capacity, daily volume,
// depletion forecasts, every terminal's rack price + contract differential +
// freight + state/federal taxes, and the carrier fleet.
//
// For each (store, grade) pair that's CRITICAL or URGENT and doesn't already
// have a load in motion (inferred from liveLoads), compute:
//   landed_cost_per_gal[terminal] = rack + diff + freight + state_tax + fed_tax
// then pick the terminal with the lowest landed cost. Compare against the
// "naive baseline" of simply using the store's assigned terminal. The per-load
// delta × volume is the dollar savings the plan captures on each line.
//
// This is a greedy heuristic — it optimizes each load independently rather
// than solving a global mixed-integer program for the whole day's plan.
// That's honest: the reasoning is transparent per row, it runs instantly,
// and the numbers are defensible to a prospect in a demo without a solver.
// For true global optimality you'd add an "AI Refine" pass calling Claude
// to spot cross-load opportunities (covered in the on-screen caveat).
function DailyPlanOptimizer({ liveLoads, planFilter, onClearPlanFilter, onOpenDispatch, onPublishDay, darkMode, C, FONT }) {
  const [expandedId, setExpandedId] = useState(null);
  // Per-row map of which terminals have their supplier sub-list expanded.
  // Key: `${rowId}:${terminalId}`, value: boolean. Kept as a flat object so
  // state updates don't need nested spreading.
  const [expandedTerminals, setExpandedTerminals] = useState({});
  const [sortKey, setSortKey] = useState("runout"); // runout | savings | cost | volume
  const [hideAssigned, setHideAssigned] = useState(false); // only show rows that switch terminals
  const [viewMode, setViewMode] = useState("loads"); // "loads" (per-row) or "trips" (consolidated)
  const [respectTerritories, setRespectTerritories] = useState(true); // default: keep loads in their assigned zone
  const [showPublishModal, setShowPublishModal] = useState(false);

  // ─── Driver assignment heuristic ────────────────────────────────────────
  // Greedy: for each trip in priority order (most savings first), pick the
  // available driver with the most HOS remaining who works for a carrier
  // with terminal access. A driver can only be assigned to one trip per
  // pass — multiple loads per driver per day come later (HOS-aware
  // multi-trip scheduling is its own optimization problem).
  const buildAssignments = (trips) => {
    if (!trips || trips.length === 0) return {};
    // Pool of available drivers across all carriers, keyed by carrier short
    const driversByCarrier = {};
    CARRIER_FLEET.forEach(c => {
      driversByCarrier[c.short] = c.tractors
        .filter(t => t.status === "AVAILABLE")
        .map(t => ({ tractor:t, carrier:c, claimed:false }))
        .sort((a,b) => (b.tractor.hos||0) - (a.tractor.hos||0)); // most HOS first
    });
    const sortedTrips = trips.slice().sort((a,b) => (b.savings||0) - (a.savings||0));
    const assignments = {}; // tripId → { carrier, tractor }
    sortedTrips.forEach(trip => {
      // Find every carrier with access to this terminal
      const eligibleCarriers = CARRIER_FLEET.filter(c =>
        c.terminalAccess?.includes(trip.terminal.id)
      );
      // Among them, find the unclaimed driver with the most HOS
      let best = null;
      eligibleCarriers.forEach(c => {
        const pool = driversByCarrier[c.short] || [];
        const cand = pool.find(d => !d.claimed);
        if (cand && (!best || (cand.tractor.hos||0) > (best.tractor.hos||0))) {
          best = cand;
        }
      });
      if (best) {
        best.claimed = true;
        assignments[trip.id] = { carrier:best.carrier, tractor:best.tractor };
      }
    });
    return assignments;
  };
  // Manual overrides: user-selected terminal for a specific (store,grade) row
  // keyed by rowId → terminalId. Takes precedence over the algorithm's pick.
  const [overrides, setOverrides] = useState({});

  const setOverride = (rowId, terminalId) => {
    setOverrides(prev => ({ ...prev, [rowId]: terminalId }));
  };
  const clearOverride = (rowId) => {
    setOverrides(prev => { const n = {...prev}; delete n[rowId]; return n; });
  };
  const clearAllOverrides = () => setOverrides({});

  // ─── Build the plan ─────────────────────────────────────────────────────
  const plan = useMemo(() => {
    // Which stores already have a load in motion? Don't re-plan those.
    const dispatched = new Set();
    liveLoads.forEach(l => {
      if (["LOADING","EN ROUTE","DELIVERING","SCHEDULED"].includes(l.status)) {
        dispatched.add(`${l.dest}|${l.grade}`);
      }
    });

    const rows = [];
    STORES.forEach(store => {
      const dep = DEPLETION.find(d => d.storeId === store.id);
      if (!dep) return;
      GRADES.forEach(grade => {
        const forecast = dep.forecast?.[grade];
        if (!forecast) return;

        // Include critical (≤1 day) and urgent (≤1.5 days) for reorder or critical level
        const needsFuel =
          (forecast.daysToCritical != null && forecast.daysToCritical <= 1) ||
          (forecast.daysToReorder  != null && forecast.daysToReorder  <= 1.5);
        if (!needsFuel) return;

        // Skip if already dispatched
        if (dispatched.has(`${store.name}|${grade}`)) return;

        // Refill volume = top off to 85%, rounded to 500-gal chunks,
        // and capped at truck compartment (16K typical)
        const capacity = store.tanks[grade] || 0;
        const current  = store.invLevel?.[grade] ?? capacity * 0.25;
        const targetFill = capacity * 0.85 - current;
        const vol = Math.max(2000, Math.min(16000, Math.round(targetFill / 500) * 500));
        if (vol <= 0) return;

        // Evaluate each terminal × supplier combination that carries this
        // grade. Freight scales with actual distance via FREIGHT_ZONES. Each
        // terminal now has 2-4 supplier options with their own rack offsets,
        // contract differentials, and spot premiums. The optimizer applies a
        // "contract pull" to bias toward suppliers that still need volume to
        // hit their monthly commitments — this protects contract economics
        // while still letting spot win when the savings are meaningful.
        const CONTRACT_PULL_PER_GAL = 0.0080; // bias toward contract if under commitment
        const options = [];
        TERMINALS.forEach(t => {
          const miles  = distMiles(t.lat, t.lng, store.lat, store.lng);
          const fz     = freightFor(t.id, miles);
          const freight= fz.rate;
          const stateTax = STATE_TAX[store.state] ?? STATE_TAX.NC;
          const suppliersAtTerm = SUPPLIERS_BY_TERMINAL[t.id] || [];
          suppliersAtTerm.forEach(sup => {
            const costInfo = supplierCostPerGal(sup, grade);
            const landed = costInfo.total + freight + stateTax + FED_TAX;
            // Contract-protection bias: suppliers under-lifted vs commitment
            // get a small effective-cost discount in the selection math, but
            // the displayed landed cost remains the real number. Spot-only
            // gets no bias. Once a contract is fully lifted (liftedMTD >=
            // commitment), the bias zeroes out for that supplier too.
            const commit = sup.monthlyCommit || 0;
            const lifted = sup.liftedMTD || 0;
            const underCommit = commit > 0 && lifted < commit;
            const commitGap = underCommit ? (commit - lifted) / commit : 0; // 0-1, higher = more urgent
            const contractBias = underCommit
              ? CONTRACT_PULL_PER_GAL * Math.min(1, commitGap * 1.5)
              : 0;
            const scoreLanded = landed - contractBias; // used only for sort/pick
            options.push({
              terminal: t, supplier: sup,
              rack: costInfo.rack,
              diff: costInfo.isSpot ? 0 : costInfo.diff,
              spotPremium: costInfo.isSpot ? costInfo.premium : 0,
              isSpot: costInfo.isSpot,
              contractStatus: sup.contractStatus,
              freight, stateTax,
              landed,               // true landed $/gal (shown in UI)
              scoreLanded,          // landed after contract bias (used for ranking)
              totalCost: landed*vol,
              miles, freightZone: fz.zone, freightBase: fz.base, freightMult: fz.mult,
              commit, lifted, underCommit, commitGap, contractBias,
            });
          });
        });
        options.sort((a,b) => a.scoreLanded - b.scoreLanded);

        const rowId      = `${store.id}-${grade}`;
        // Baseline = store's assigned terminal + its primary supplier. Falls
        // back to cheapest option at that terminal if no primary exists.
        const baseline = options.find(o =>
          o.terminal.id === store.terminal && o.supplier.contractStatus === "primary"
        ) || options.find(o => o.terminal.id === store.terminal) || options[0];
        // Algorithm's pick — respects the territory toggle. When ON, algo
        // restricted to the assigned terminal (across its suppliers). When
        // OFF, it picks the lowest-scored option across all terminals and
        // suppliers. Manual overrides still work either way.
        const bestAtTerminal = options.find(o => o.terminal.id === store.terminal) || baseline;
        const crossZoneBest = options[0]; // best across all zones and suppliers
        const algoPick   = respectTerritories ? bestAtTerminal : crossZoneBest;
        const overrideId = overrides[rowId];
        // Override key is now "terminalId:supplierId" to identify the exact option
        const chosen     = overrideId
          ? (options.find(o => `${o.terminal.id}:${o.supplier.id}` === overrideId) || algoPick)
          : algoPick;
        const isOverridden = `${chosen.terminal.id}:${chosen.supplier.id}` !== `${algoPick.terminal.id}:${algoPick.supplier.id}`;
        const isSwitch     = chosen.terminal.id !== baseline.terminal.id || chosen.supplier.id !== baseline.supplier.id;
        // Foregone vs cross-zone optimal — what you give up by respecting
        // territories. Surfaced in the hero banner.
        const territoryForegonePerGal = baseline.landed - crossZoneBest.landed;
        const territoryForegoneTotal  = territoryForegonePerGal * vol;

        // Pick best available carrier with access to the chosen terminal
        const carriers = CARRIER_FLEET
          .filter(c => c.available > 0 && c.terminalAccess.includes(chosen.terminal.id))
          .sort((a,b) => (a.rateBase + a.ratePerMile) - (b.rateBase + b.ratePerMile));
        const carrier = carriers[0] || null;

        // Savings measured against assigned-terminal baseline.
        // Forgone savings = how much the user gave up by not following the algorithm.
        const savingsPerGal  = baseline.landed - chosen.landed;
        const savingsTotal   = savingsPerGal * vol;
        const foregonePerGal = chosen.landed - algoPick.landed;
        const foregoneTotal  = foregonePerGal * vol;

        // Reason text — four modes depending on how chosen was selected.
        // All include supplier so the procurement person sees the full story.
        const termSup = (o) => `${o.terminal.short}/${o.supplier.short}`;
        let reason;
        if (isOverridden) {
          const forgoneStr = foregonePerGal > 0
            ? ` Foregoes $${foregonePerGal.toFixed(4)}/gal ($${Math.round(foregoneTotal).toLocaleString()} total) vs optimal ${termSup(algoPick)}.`
            : "";
          reason = `Manual override: ${termSup(chosen)} selected instead of algorithm pick ${termSup(algoPick)}.${forgoneStr}`;
        } else if (!isSwitch) {
          reason = `${termSup(baseline)} is your assigned pick and also the lowest-landed option today. No switch saves money on this load.`;
        } else {
          const rackDelta    = (baseline.rack - chosen.rack).toFixed(4);
          const freightDelta = (baseline.freight - chosen.freight).toFixed(4);
          const baseCarryCost = baseline.isSpot ? baseline.spotPremium : baseline.diff;
          const chosenCarryCost = chosen.isSpot ? chosen.spotPremium : chosen.diff;
          const diffDelta    = (baseCarryCost - chosenCarryCost).toFixed(4);
          const parts = [];
          if (+rackDelta > 0)    parts.push(`rack $${rackDelta} lower`);
          if (+rackDelta < 0)    parts.push(`rack $${Math.abs(rackDelta).toFixed(4)} higher`);
          if (+freightDelta > 0) parts.push(`freight $${freightDelta} lower`);
          if (+freightDelta < 0) parts.push(`freight $${Math.abs(freightDelta).toFixed(4)} higher`);
          if (+diffDelta > 0)    parts.push(chosen.isSpot ? `spot premium $${diffDelta} better` : `contract diff $${diffDelta} better`);
          // Call out supplier change vs terminal change explicitly
          const sameTerminal = baseline.terminal.id === chosen.terminal.id;
          const verb = sameTerminal ? `Supplier switch at ${chosen.terminal.short}` : `Switch`;
          reason = `${verb} ${termSup(baseline)} → ${termSup(chosen)}: ${parts.join(" · ")}. Net $${savingsPerGal.toFixed(4)}/gal.`;
        }

        // Algorithmic savings = baseline vs algorithm's pick (doesn't move
        // when user overrides). Used for stable sort order so rows don't
        // jump around while a user is editing their picks.
        const algoSavingsTotal = (baseline.landed - algoPick.landed) * vol;

        // ─── Runout time ─────────────────────────────────────────────────
        // Hours until store dry-runs on this grade (current inv ÷ daily vol).
        // Uses EFFECTIVE daily volume — for Regular and Premium this includes
        // the share pulled into the Plus blend, which is the actual draw rate
        // on the tank. A store with heavy Plus sales depletes Reg/Prem faster
        // than its pure-Reg/Prem sales numbers would suggest.
        const dailyVol = (store.effectiveDailyVol?.[grade]) || store.dailyVol[grade] || 1;
        const currentInv = store.invLevel?.[grade] ?? 0;
        const runoutHours = (currentInv / dailyVol) * 24;
        const runoutDays = Math.floor(runoutHours / 24);
        const runoutHrs  = Math.floor(runoutHours % 24);
        const runoutLabel = runoutDays > 0
          ? `${runoutDays}d ${runoutHrs}h`
          : `${runoutHrs}h`;
        // Color band based on urgency
        const runoutColor = runoutHours <= 12 ? "#DC2626"
                          : runoutHours <= 24 ? "#EA580C"
                          : runoutHours <= 36 ? "#F59E0B"
                          : "#16A34A";

        // ─── Dispatch window ─────────────────────────────────────────────
        // Latest acceptable arrival = runout time minus a 4-hour safety
        // buffer (truck staging, loading, drive). Earliest = store opens.
        const win = store.receivingWindow || { open: 0, close: 24, label: "24/7" };
        const latestArrivalHrs = Math.max(2, runoutHours - 4);
        // Format as "Now - HH:MM" for today, or "Now - Apr DD HH:MM" if multi-day
        const fmtArrival = (hrsFromNow) => {
          const d = new Date(Date.now() + hrsFromNow * 3600 * 1000);
          const isToday = d.toDateString() === new Date().toDateString();
          const time = d.toLocaleTimeString("en-US", { hour:"numeric", minute:"2-digit", hour12:true });
          if (isToday) return time;
          const date = d.toLocaleDateString("en-US", { month:"short", day:"numeric" });
          return `${date} ${time}`;
        };
        const dispatchWindow = {
          earliest: "Now",
          latest: fmtArrival(latestArrivalHrs),
          windowLabel: win.label,
          isAfterHours: win.close < 24,
          windowOpen: win.open,
          windowClose: win.close,
        };

        rows.push({
          id: rowId,
          store, grade, vol,
          chosen, baseline, algoPick, isSwitch, isOverridden,
          optimalCost: chosen.totalCost, baselineCost: baseline.totalCost,
          savingsPerGal, savingsTotal,
          algoSavingsTotal,
          foregonePerGal, foregoneTotal,
          territoryForegonePerGal, territoryForegoneTotal,
          crossZoneBest,
          reason, carrier, alternatives: options,
          priority: forecast.daysToCritical <= 1 ? "CRITICAL" : "URGENT",
          daysToCritical: forecast.daysToCritical,
          // Runout & window
          runoutHours, runoutLabel, runoutColor,
          dispatchWindow,
        });
      });
    });

    // Sort — uses algorithmic (pre-override) values so rows keep their
    // position when a user changes their pick. Sort order represents
    // inherent optimization opportunity, not post-override state.
    const sorted = rows.slice().sort((a,b) => {
      if (sortKey === "runout")  return a.runoutHours - b.runoutHours;       // soonest first
      if (sortKey === "savings") return b.algoSavingsTotal - a.algoSavingsTotal;
      if (sortKey === "cost")    return b.algoPick.totalCost - a.algoPick.totalCost;
      if (sortKey === "volume")  return b.vol - a.vol;
      return 0;
    });

    // Totals
    const totalLoads    = sorted.length;
    const totalGallons  = sorted.reduce((a,r) => a + r.vol, 0);
    const totalOptimal  = sorted.reduce((a,r) => a + r.optimalCost, 0);
    const totalBaseline = sorted.reduce((a,r) => a + r.baselineCost, 0);
    const totalSavings  = totalBaseline - totalOptimal;
    const totalForegone = sorted.reduce((a,r) => a + r.foregoneTotal, 0);
    const totalTerritoryForegone = sorted.reduce((a,r) => a + (r.territoryForegoneTotal || 0), 0);
    const territoryCrossings = sorted.filter(r => r.crossZoneBest && r.crossZoneBest.terminal.id !== r.baseline.terminal.id).length;
    const avgSavingsPerGal = totalGallons > 0 ? totalSavings / totalGallons : 0;
    const switchCount    = sorted.filter(r => r.isSwitch).length;
    const overrideCount  = sorted.filter(r => r.isOverridden).length;

    // ─── Compartment pocket planning ──────────────────────────────────
    // Group rows into multi-stop trips where compartment volumes allow.
    // Each row only participates in trip planning if it's not been
    // overridden to a different terminal manually (we honor the user's
    // override but trip-plan around it).
    const trips = planCompartmentTrips(sorted, CARRIER_FLEET);
    const consolidatedTrips = trips.filter(t => t.isMultiStop).length;
    const tripSavings = trips.reduce((s,t) => s + (t.savings || 0), 0);

    return {
      rows:sorted, trips, consolidatedTrips, tripSavings,
      totalLoads, totalGallons, totalOptimal, totalBaseline, totalSavings, totalForegone,
      totalTerritoryForegone, territoryCrossings,
      avgSavingsPerGal, switchCount, overrideCount,
    };
  }, [liveLoads, sortKey, overrides, respectTerritories]);

  const preFilterRows = hideAssigned ? plan.rows.filter(r => r.isSwitch) : plan.rows;
  // Apply planFilter when present — narrows the view to rows that could route
  // to the target terminal (and grade, if specified). "Could route" = the row's
  // alternatives include the target terminal, OR it's already assigned there.
  // This keeps the view focused on actionable loads for the incoming context.
  const visibleRows = planFilter
    ? preFilterRows.filter(r => {
        const terminalMatch = r.chosen.terminal.id === planFilter.terminalId
          || (r.alternatives && r.alternatives.some(a => a.terminal.id === planFilter.terminalId));
        const gradeMatch = !planFilter.grade || r.grade === planFilter.grade;
        return terminalMatch && gradeMatch;
      })
    : preFilterRows;

  // ─── Render ──────────────────────────────────────────────────────────────
  const moneyStyle = { fontFamily:"Arial,sans-serif", fontWeight:800 };
  const savingsGreen = "#16A34A";
  const savingsRed = "#DC2626";

  return (
    <div style={{display:"flex", flexDirection:"column", gap:12}}>

      {/* ─── Incoming-context filter banner ─────────────────────────────── */}
      {planFilter && (
        <div style={{
          padding:"12px 16px", borderRadius:10,
          background: darkMode ? "rgba(200,164,74,.08)" : "#FFF9E6",
          border: `1.5px solid ${C.gold}`,
          display:"flex", alignItems:"center", gap:14,
        }}>
          <div style={{
            width:32, height:32, borderRadius:"50%",
            background:C.gold, color:"#0D1B2A",
            display:"flex", alignItems:"center", justifyContent:"center",
            fontSize:16, fontWeight:800, flexShrink:0, fontFamily:FONT,
          }}>
            ›
          </div>
          <div style={{flex:1, minWidth:0}}>
            <div style={{fontSize:10, fontWeight:800, color:C.gold, letterSpacing:.6, textTransform:"uppercase", marginBottom:2}}>
              Filtered view — {planFilter.reason === "bump-lifts" ? "from Contracts page" : "from Today's Best Buy"}
            </div>
            <div style={{fontSize:12, color:C.textPri, fontFamily:FONT, fontWeight:600}}>
              {planFilter.message}
            </div>
            <div style={{fontSize:10, color:C.textSec, marginTop:3, fontFamily:FONT}}>
              Showing {visibleRows.length} of {preFilterRows.length} loads that can route through this terminal{planFilter.grade ? ` for ${planFilter.grade}` : ""}.
            </div>
          </div>
          <button
            onClick={onClearPlanFilter}
            style={{
              padding:"6px 14px", borderRadius:6, border:`1px solid ${C.gold}`,
              background:"transparent", color: C.gold,
              fontSize:10.5, fontWeight:700, cursor:"pointer", fontFamily:FONT,
              whiteSpace:"nowrap", flexShrink:0,
            }}>
            Clear filter ×
          </button>
        </div>
      )}

      {/* ─── Hero savings banner ───────────────────────────────────────── */}
      <div style={{
        padding:"16px 20px", borderRadius:10,
        background: darkMode
          ? "linear-gradient(135deg, rgba(22,163,74,.15), rgba(200,164,74,.08))"
          : "linear-gradient(135deg, #F0FDF4, #FFFDF0)",
        border: `1px solid ${darkMode ? "rgba(22,163,74,.35)" : "#BBF7D0"}`,
        display:"flex", alignItems:"center", gap:20,
      }}>
        <div style={{
          width:44, height:44, borderRadius:"50%",
          background: plan.totalSavings > 0 ? savingsGreen : C.textMut,
          color:"#fff", display:"flex", alignItems:"center", justifyContent:"center",
          fontSize:22, fontWeight:800, flexShrink:0, fontFamily:"Arial,sans-serif",
        }}>$</div>
        <div style={{flex:1, minWidth:0}}>
          <div style={{fontSize:9.5, fontWeight:800, color: plan.totalSavings > 0 ? savingsGreen : C.textSec, letterSpacing:.8, textTransform:"uppercase", marginBottom:3}}>
            Projected savings today
          </div>
          <div style={{fontSize:22, ...moneyStyle, color: plan.totalSavings > 0 ? savingsGreen : C.textPri}}>
            ${Math.round(plan.totalSavings).toLocaleString()}
            <span style={{fontSize:13, fontWeight:500, color:C.textSec, marginLeft:10, letterSpacing:.2}}>
              · ${plan.avgSavingsPerGal.toFixed(4)}/gal avg · {plan.switchCount} of {plan.totalLoads} loads re-routed
            </span>
          </div>
          <div style={{fontSize:11, color:C.textSec, marginTop:4}}>
            Baseline ${Math.round(plan.totalBaseline).toLocaleString()} → Optimized ${Math.round(plan.totalOptimal).toLocaleString()}.
            {respectTerritories
              ? " Greedy per-load selection within each store's assigned territory."
              : " Greedy per-load selection across all terminals (territories ignored)."}
            {plan.tripSavings > 0 && (
              <span style={{marginLeft:6, color:"#16A34A", fontWeight:600}}>
                · + ${Math.round(plan.tripSavings).toLocaleString()} more from consolidating {plan.consolidatedTrips} multi-stop trip{plan.consolidatedTrips>1?"s":""}.
              </span>
            )}
            {respectTerritories && plan.totalTerritoryForegone > 1 && (
              <span style={{marginLeft:6, color:"#EA580C", fontWeight:600}}>
                · Unlock ${Math.round(plan.totalTerritoryForegone).toLocaleString()} more by allowing {plan.territoryCrossings} zone-crossing{plan.territoryCrossings>1?"s":""}.
              </span>
            )}
            {plan.totalForegone > 0 && (
              <span style={{marginLeft:6, color:"#0D9488", fontWeight:600}}>
                · Manual overrides cost ${Math.round(plan.totalForegone).toLocaleString()} in foregone savings.
              </span>
            )}
          </div>
        </div>
        <div style={{position:"relative", flexShrink:0}}>
          <button
            onClick={()=>setShowPublishModal(true)}
            disabled={plan.trips.length === 0}
            style={{
              padding:"7px 14px", borderRadius:7, border:"none",
              background: plan.trips.length === 0
                ? (darkMode?"rgba(255,255,255,.08)":"#E5E9EF")
                : "#0D1B2A",
              color: plan.trips.length === 0 ? C.textMut : "#fff",
              fontSize:11.5, fontWeight:700, letterSpacing:.2,
              cursor: plan.trips.length === 0 ? "not-allowed" : "pointer",
              fontFamily:FONT,
              boxShadow: plan.trips.length === 0 ? "none" : "0 2px 6px rgba(200,164,74,.45)",
              whiteSpace:"nowrap",
            }}
            title={plan.trips.length === 0 ? "No trips to publish" : `Auto-assign drivers and publish ${plan.trips.length} trip${plan.trips.length!==1?"s":""} to schedule`}>
            Optimize Day
          </button>
          {/* Trip count badge — sits at the top-right of the button */}
          {plan.trips.length > 0 && (
            <span style={{
              position:"absolute", top:-7, right:-9,
              minWidth:20, height:20, padding:"0 6px",
              borderRadius:10,
              background: darkMode ? "#0D1B2A" : "#fff",
              border:`1.5px solid #F4D398`,
              color:"#F4D398",
              fontSize:10, fontWeight:800, lineHeight:"17px",
              fontFamily:"Arial,sans-serif",
              textAlign:"center",
              boxShadow:"0 1px 4px rgba(0,0,0,.18)",
              pointerEvents:"none",
            }}>
              {plan.trips.length}
            </span>
          )}
        </div>
      </div>

      {/* ─── KPI strip ─────────────────────────────────────────────────── */}
      <div style={{display:"flex", gap:8}}>
        {[
          { label:"Loads planned",    val:plan.totalLoads, sub:`${plan.switchCount} re-routed`, color:"#3B82F6" },
          { label:"Gallons planned",  val:`${(plan.totalGallons/1000).toFixed(0)}K`, sub:"across all grades", color:"#0891B2" },
          { label:"Total optimised",  val:`$${(plan.totalOptimal/1000).toFixed(0)}K`, sub:`avg $${(plan.totalOptimal/plan.totalGallons||0).toFixed(3)}/gal`, color:C.gold },
          { label:"Savings vs default", val:`$${Math.round(plan.totalSavings).toLocaleString()}`, sub:"vs assigned-terminal baseline", color: plan.totalSavings > 0 ? savingsGreen : C.textMut },
        ].map((k,i) => <KpiCard key={i} {...k} C={C} darkMode={darkMode}/>)}
      </div>

      {/* ─── Controls ─────────────────────────────────────────────────── */}
      <div style={{display:"flex", alignItems:"center", gap:10, flexWrap:"wrap"}}>
        {/* View mode toggle — Loads (one row per delivery) vs Trips (consolidated multi-stop) */}
        <div style={{
          display:"inline-flex", borderRadius:7,
          border:`1px solid ${C.cardBord}`, overflow:"hidden",
        }}>
          {[
            {k:"loads", l:"Loads view", n:plan.totalLoads},
            {k:"trips", l:"Trips view", n:plan.trips.length, badge:plan.consolidatedTrips},
          ].map(opt => {
            const on = viewMode === opt.k;
            return (
              <button key={opt.k} onClick={()=>setViewMode(opt.k)}
                style={{
                  padding:"5px 12px", border:"none",
                  background: on ? C.gold : (darkMode ? "transparent" : "#fff"),
                  color: on ? "#fff" : C.textSec,
                  fontSize:11, fontWeight: on ? 700 : 500,
                  cursor:"pointer", fontFamily:FONT,
                  display:"flex", alignItems:"center", gap:6,
                }}>
                {opt.l}
                <span style={{fontSize:9, opacity:.85, fontWeight:600}}>{opt.n}</span>
                {opt.badge > 0 && opt.k === "trips" && (
                  <span style={{
                    fontSize:8.5, fontWeight:800,
                    background: on ? "rgba(255,255,255,.25)" : "#16A34A",
                    color: on ? "#fff" : "#fff",
                    padding:"1px 5px", borderRadius:8, letterSpacing:.4,
                  }}>+{opt.badge} multi</span>
                )}
              </button>
            );
          })}
        </div>
        <div style={{width:1, height:20, background:C.cardBord, margin:"0 4px"}}/>
        <span style={{fontSize:10.5, color:C.textSec, fontFamily:FONT, fontWeight:600}}>Sort:</span>
        {[
          {k:"runout",  l:"Soonest runout"},
          {k:"savings", l:"Biggest savings"},
          {k:"cost",    l:"Biggest loads"},
          {k:"volume",  l:"Most gallons"},
        ].map(opt => (
          <button key={opt.k} onClick={()=>setSortKey(opt.k)}
            style={{
              padding:"4px 10px", borderRadius:6,
              border:`1px solid ${sortKey===opt.k ? C.gold : C.cardBord}`,
              background: sortKey===opt.k ? (darkMode?"rgba(200,164,74,.12)":"#FFFDF0") : "transparent",
              color: sortKey===opt.k ? C.gold : C.textSec,
              fontSize:10.5, fontWeight: sortKey===opt.k ? 700 : 400,
              cursor:"pointer", fontFamily:FONT,
            }}>
            {opt.l}
          </button>
        ))}
        <div style={{width:1, height:20, background:C.cardBord, margin:"0 4px"}}/>
        {/* Territory toggle — keep loads in their assigned terminal's zone */}
        <button onClick={()=>setRespectTerritories(!respectTerritories)}
          title={respectTerritories
            ? "Loads stay within their assigned terminal's territory. Click to allow zone-crossing for max savings."
            : "Loads can cross territory lines to find the lowest-landed terminal. Click to lock back to assigned zones."}
          style={{
            padding:"4px 10px", borderRadius:6,
            border:`1px solid ${respectTerritories ? "#3E6387" : "#EA580C"}`,
            background: respectTerritories
              ? (darkMode?"rgba(62,99,135,.18)":"#EFF6FF")
              : (darkMode?"rgba(234,88,12,.15)":"#FFF7ED"),
            color: respectTerritories ? "#3E6387" : "#EA580C",
            fontSize:10.5, fontWeight: 700,
            cursor:"pointer", fontFamily:FONT,
            display:"inline-flex", alignItems:"center", gap:5,
          }}>
          <span style={{fontSize:10}}>{respectTerritories ? "LOCKED" : "UNLOCKED"}</span>
          {respectTerritories ? "Territories: respected" : "Territories: crossing allowed"}
        </button>
        <button onClick={()=>setHideAssigned(!hideAssigned)}
          style={{
            padding:"4px 10px", borderRadius:6,
            border:`1px solid ${hideAssigned ? C.gold : C.cardBord}`,
            background: hideAssigned ? (darkMode?"rgba(200,164,74,.12)":"#FFFDF0") : "transparent",
            color: hideAssigned ? C.gold : C.textSec,
            fontSize:10.5, fontWeight: hideAssigned ? 700 : 400,
            cursor:"pointer", fontFamily:FONT,
          }}>
          {hideAssigned ? "• " : ""}Only show re-routed loads
        </button>
        {plan.overrideCount > 0 && (
          <button onClick={clearAllOverrides}
            style={{
              padding:"4px 10px", borderRadius:6,
              border:`1px solid ${darkMode?"rgba(13,148,136,.45)":"#5EEAD4"}`,
              background:darkMode?"rgba(13,148,136,.12)":"#F0FDFA",
              color:"#0D9488", fontSize:10.5, fontWeight:700,
              cursor:"pointer", fontFamily:FONT,
            }}>
            ↺ Reset {plan.overrideCount} manual override{plan.overrideCount>1?"s":""}
          </button>
        )}
        <div style={{marginLeft:"auto", fontSize:10.5, color:C.textMut, fontFamily:FONT}}>
          Showing {visibleRows.length} of {plan.totalLoads}
          {plan.overrideCount > 0 && (
            <span style={{color:"#0D9488", fontWeight:700, marginLeft:8}}>
              · {plan.overrideCount} manual
            </span>
          )}
        </div>
      </div>

      {/* ─── Plan table (loads view) ──────────────────────────────────── */}
      {viewMode === "loads" && (
      <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden"}}>
        {/* Column headers */}
        <div style={{
          display:"grid", gridTemplateColumns:"1.1fr 70px 105px 65px 80px 60px 110px 100px 85px 30px",
          gap:8, padding:"10px 14px",
          background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
          borderBottom:`1px solid ${C.cardBord}`,
          fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase",
          fontFamily:FONT,
        }}>
          <div>Store · Grade</div>
          <div style={{textAlign:"right"}}>Runout</div>
          <div>Dispatch by</div>
          <div style={{textAlign:"right"}}>Vol</div>
          <div>Terminal</div>
          <div style={{textAlign:"right"}}>Miles</div>
          <div>Carrier</div>
          <div style={{textAlign:"right"}}>Landed cost</div>
          <div style={{textAlign:"right"}}>Savings</div>
          <div/>
        </div>

        {/* Rows */}
        {visibleRows.length === 0 ? (
          <div style={{padding:"40px 20px", textAlign:"center", color:C.textMut, fontSize:12, fontFamily:FONT}}>
            {plan.totalLoads === 0
              ? "No stores meet today's dispatch threshold. All tanks above reorder level and no loads pending."
              : "All planned loads use their assigned terminal — no re-routing saves money today."}
          </div>
        ) : visibleRows.map((r,i) => {
          const isOpen = expandedId === r.id;
          const priorityColor = r.priority === "CRITICAL" ? "#EF4444" : "#F59E0B";
          return (
            <div key={r.id} style={{borderBottom: i<visibleRows.length-1 ? `1px solid ${C.cardBord}` : "none"}}>
              {/* Main row */}
              <div onClick={()=>setExpandedId(isOpen ? null : r.id)}
                style={{
                  display:"grid", gridTemplateColumns:"1.1fr 70px 105px 65px 80px 60px 110px 100px 85px 30px",
                  gap:8, padding:"12px 14px", alignItems:"center",
                  cursor:"pointer", transition:"background .12s",
                  background: isOpen ? (darkMode?"rgba(200,164,74,.06)":"#F8FAFB") : "transparent",
                }}
                onMouseEnter={e=>{ if(!isOpen) e.currentTarget.style.background = darkMode?"rgba(255,255,255,.02)":"#FAFBFD"; }}
                onMouseLeave={e=>{ if(!isOpen) e.currentTarget.style.background = "transparent"; }}>
                {/* Store + grade */}
                <div style={{minWidth:0}}>
                  <div style={{display:"flex", alignItems:"center", gap:6, marginBottom:2}}>
                    <span style={{fontSize:8.5, fontWeight:800, padding:"1.5px 5px", borderRadius:3,
                      background:`${priorityColor}22`, color:priorityColor,
                      letterSpacing:.4, flexShrink:0, border:`1px solid ${priorityColor}30`}}>
                      {r.priority}
                    </span>
                    <span style={{fontSize:11.5, fontWeight:700, color:C.textPri, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                      {r.store.name}
                    </span>
                  </div>
                  <div style={{fontSize:10, color:C.textSec, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                    {r.store.city}, {r.store.state} · {r.grade}
                  </div>
                </div>
                {/* Runout — colored badge with hours */}
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:12, fontWeight:800, color:r.runoutColor, fontFamily:"Arial,sans-serif"}}>
                    {r.runoutLabel}
                  </div>
                  <div style={{fontSize:9, color:C.textMut, marginTop:1}}>to dry-run</div>
                </div>
                {/* Dispatch window */}
                <div style={{minWidth:0}}>
                  <div style={{fontSize:10.5, fontWeight:600, color:C.textPri, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                    Now → {r.dispatchWindow.latest}
                  </div>
                  <div style={{fontSize:9, color: r.dispatchWindow.isAfterHours ? "#EA580C" : C.textMut, marginTop:1, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}
                    title={r.dispatchWindow.isAfterHours ? `Receiving hours: ${r.dispatchWindow.windowLabel}` : "24/7 receiving"}>
                    {r.dispatchWindow.isAfterHours ? `${r.dispatchWindow.windowLabel}` : "24/7"}
                  </div>
                </div>
                {/* Volume */}
                <div style={{textAlign:"right", fontSize:11, fontWeight:600, color:C.textPri, ...moneyStyle}}>
                  {(r.vol/1000).toFixed(0)}K
                  <div style={{fontSize:9, fontWeight:400, color:C.textMut}}>gal</div>
                </div>
                {/* Terminal (with switch / override indicator) */}
                <div>
                  <div style={{display:"flex", alignItems:"center", gap:5, flexWrap:"wrap"}}>
                    {(() => {
                      const zone = TERMINAL_ZONE[r.chosen.terminal.id];
                      return zone ? (
                        <span style={{
                          fontSize:8, fontWeight:800, padding:"1px 5px", borderRadius:3,
                          background: zone.color, color:"#fff", letterSpacing:.3,
                          flexShrink:0,
                        }}>Z{zone.id}</span>
                      ) : null;
                    })()}
                    <span style={{fontSize:11.5, fontWeight:700,
                      color: r.isOverridden ? "#0D9488" : (r.isSwitch ? C.gold : C.textPri),
                      fontFamily:"Arial,sans-serif"}}>
                      {r.chosen.terminal.short}
                    </span>
                    {(() => {
                      const brand = supplierBrand(r.chosen.supplier.name);
                      return (
                        <span title={`${r.chosen.supplier.name} · ${r.chosen.supplier.contractStatus}`} style={{
                          display:"inline-flex", alignItems:"center", gap:4,
                          fontSize:8.5, fontWeight:800,
                          color: brand.primary,
                          background: `${brand.primary}20`,
                          padding:"1px 5px 1px 2px", borderRadius:3, letterSpacing:.4,
                          border:`1px solid ${brand.primary}50`,
                        }}>
                          <SupplierLogo supplierName={r.chosen.supplier.name} supplierShort={r.chosen.supplier.short} size={12}/>
                          {r.chosen.supplier.short}
                          {r.chosen.isSpot && <span style={{color:"#EA580C", fontWeight:800}}>·SPOT</span>}
                          {!r.chosen.isSpot && r.chosen.contractStatus === "secondary" && <span style={{opacity:.75}}>·2°</span>}
                        </span>
                      );
                    })()}
                    {r.isSwitch && (
                      <span style={{fontSize:9, color:C.textMut, textDecoration:"line-through"}}>
                        {r.baseline.terminal.short}
                      </span>
                    )}
                    {r.isOverridden && (
                      <span title="Manual override" style={{
                        fontSize:8, fontWeight:800, color:"#0D9488",
                        background:darkMode?"rgba(13,148,136,.15)":"#F0FDFA",
                        padding:"1px 5px", borderRadius:3, letterSpacing:.5,
                        border:`1px solid ${darkMode?"rgba(13,148,136,.35)":"#99F6E4"}`,
                      }}>MANUAL</span>
                    )}
                  </div>
                  <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>
                    {r.isOverridden ? "you chose" : (r.isSwitch ? "re-routed" : "assigned")}
                  </div>
                </div>
                {/* Miles — straight-line distance from chosen terminal to store */}
                {(() => {
                  const miles = distMiles(
                    r.chosen.terminal.lat, r.chosen.terminal.lng,
                    r.store.lat, r.store.lng
                  );
                  // Color the figure if the chosen route is meaningfully farther
                  // than the assigned-terminal route — surface long hauls so the
                  // dispatcher sees the freight trade-off implied by re-routing.
                  const baselineMiles = distMiles(
                    r.baseline.terminal.lat, r.baseline.terminal.lng,
                    r.store.lat, r.store.lng
                  );
                  const milesDelta = miles - baselineMiles;
                  const milesColor = milesDelta > 30 ? "#EA580C"
                                   : milesDelta > 15 ? "#F59E0B"
                                   : C.textPri;
                  return (
                    <div style={{textAlign:"right"}}>
                      <div style={{fontSize:11.5, fontWeight:700, color:milesColor, fontFamily:"Arial,sans-serif"}}>
                        {miles.toFixed(0)}
                      </div>
                      <div style={{fontSize:9, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                        {r.isSwitch && Math.abs(milesDelta) >= 1
                          ? `${milesDelta > 0 ? "+" : ""}${milesDelta.toFixed(0)} vs assigned`
                          : "one-way"}
                      </div>
                    </div>
                  );
                })()}
                {/* Carrier */}
                <div style={{minWidth:0}}>
                  {r.carrier ? (
                    <>
                      <div style={{fontSize:11, fontWeight:600, color:C.textPri, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                        {r.carrier.short}
                      </div>
                      <div style={{fontSize:9.5, color:C.textMut}}>
                        {r.carrier.available} trucks ready
                      </div>
                    </>
                  ) : (
                    <div style={{fontSize:10, color:"#EF4444", fontWeight:600}}>No carrier available</div>
                  )}
                </div>
                {/* Landed cost */}
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:11.5, ...moneyStyle, color:C.textPri}}>
                    ${Math.round(r.optimalCost).toLocaleString()}
                  </div>
                  <div style={{fontSize:9.5, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                    ${r.chosen.landed.toFixed(4)}/gal
                  </div>
                </div>
                {/* Savings */}
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:12, ...moneyStyle, color: r.savingsTotal > 0 ? savingsGreen : C.textMut}}>
                    {r.savingsTotal > 0 ? "+" : ""}${Math.round(r.savingsTotal).toLocaleString()}
                  </div>
                  <div style={{fontSize:9, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                    {r.savingsPerGal > 0 ? `+$${r.savingsPerGal.toFixed(4)}/gal` : "no switch"}
                  </div>
                </div>
                {/* Expand chevron */}
                <div style={{textAlign:"center", color:C.textMut, fontSize:11, fontFamily:"Arial,sans-serif"}}>
                  {isOpen ? "▾" : "▸"}
                </div>
              </div>

              {/* Expanded reasoning */}
              {isOpen && (
                <div style={{
                  padding:"12px 18px 16px 18px",
                  background:darkMode?"rgba(200,164,74,.04)":"#F8FAFB",
                  borderTop:`1px solid ${C.cardBord}`,
                }}>
                  <div style={{fontSize:9.5, fontWeight:800, color:C.gold, letterSpacing:.8, textTransform:"uppercase", marginBottom:6}}>
                    Why this terminal
                  </div>
                  <div style={{fontSize:11.5, color:C.textPri, fontFamily:FONT, marginBottom:12, lineHeight:1.5}}>
                    {r.reason}
                  </div>

                  {/* All terminals ranked */}
                  <div style={{fontSize:9.5, fontWeight:800, color:C.textMut, letterSpacing:.8, textTransform:"uppercase", marginBottom:6}}>
                    All terminal options ({r.alternatives.length})
                  </div>
                  <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:6, overflow:"hidden"}}>
                    <div style={{
                      display:"grid", gridTemplateColumns:"40px 1fr 60px 70px 70px 70px 75px 75px 70px",
                      gap:8, padding:"6px 10px", fontSize:9,
                      background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                      borderBottom:`1px solid ${C.cardBord}`,
                      color:C.textMut, fontWeight:800, letterSpacing:.5, textTransform:"uppercase",
                    }}>
                      <div>Rank</div>
                      <div>Terminal · Supplier</div>
                      <div style={{textAlign:"right"}}>Miles</div>
                      <div style={{textAlign:"right"}}>Rack</div>
                      <div style={{textAlign:"right"}}>+ Diff/Spot</div>
                      <div style={{textAlign:"right"}}>+ Freight</div>
                      <div style={{textAlign:"right"}}>= Landed</div>
                      <div style={{textAlign:"right"}}>vs best</div>
                      <div style={{textAlign:"center"}}>Action</div>
                    </div>
                    {(() => {
                      // Group alternatives by terminal — each terminal row shows
                      // its best supplier, click to expand to see all suppliers
                      // at that terminal. Two-tier structure prevents the 12-24
                      // row flood a flat list would produce.
                      const byTerminal = {};
                      r.alternatives.forEach(alt => {
                        (byTerminal[alt.terminal.id] = byTerminal[alt.terminal.id] || []).push(alt);
                      });
                      // Order terminals by their best supplier's score
                      const terminalGroups = Object.values(byTerminal)
                        .map(group => group.slice().sort((a,b) => a.scoreLanded - b.scoreLanded))
                        .sort((a,b) => a[0].scoreLanded - b[0].scoreLanded);

                      return terminalGroups.map((group, gi) => {
                        const termBest = group[0];
                        const termId = termBest.terminal.id;
                        const isTermExpanded = expandedTerminals[`${r.id}:${termId}`];
                        return (
                          <div key={termId} style={{borderBottom: gi<terminalGroups.length-1 ? `1px solid ${C.cardBord}` : "none"}}>
                            {group.map((alt, ai) => {
                              const isFirstInGroup = ai === 0;
                              // Hide non-first rows unless terminal is expanded
                              if (!isFirstInGroup && !isTermExpanded) return null;
                              const altKey = `${alt.terminal.id}:${alt.supplier.id}`;
                              const chosenKey = `${r.chosen.terminal.id}:${r.chosen.supplier.id}`;
                              const algoKey = `${r.algoPick.terminal.id}:${r.algoPick.supplier.id}`;
                              const baselineKey = `${r.baseline.terminal.id}:${r.baseline.supplier.id}`;
                              const isChosen   = altKey === chosenKey;
                              const isAlgoPick = altKey === algoKey;
                              const isAssigned = altKey === baselineKey;
                              const deltaFromBest = alt.landed - r.algoPick.landed;
                              const altMiles = distMiles(alt.terminal.lat, alt.terminal.lng, r.store.lat, r.store.lng);
                              const milesColor = altMiles > 200 ? "#EA580C"
                                               : altMiles > 120 ? "#F59E0B"
                                               : C.textSec;
                              // Contract status badge color
                              const statusColor = alt.contractStatus === "primary"   ? "#16A34A"
                                                 : alt.contractStatus === "secondary" ? "#F4D398"
                                                 : "#EA580C"; // spot-only
                              const statusBg = alt.contractStatus === "primary"   ? (darkMode?"rgba(22,163,74,.12)":"#F0FDF4")
                                              : alt.contractStatus === "secondary" ? (darkMode?"rgba(200,164,74,.12)":"#F8FAFB")
                                              : (darkMode?"rgba(234,88,12,.12)":"#FFF7ED");
                              return (
                                <div key={altKey}
                                  onClick={(e)=>{
                                    // Click on the row: set override. Click on the
                                    // expand chevron (first row only): toggle group.
                                    if (isChosen) return;
                                    setOverride(r.id, altKey);
                                  }}
                                  style={{
                                    display:"grid", gridTemplateColumns:"40px 1fr 60px 70px 80px 70px 75px 75px 70px",
                                    gap:8, padding:"7px 10px", fontSize:10.5,
                                    background: isChosen ? (darkMode?"rgba(13,148,136,.10)":"#F0FDFA")
                                              : isAlgoPick ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4")
                                              : isFirstInGroup ? "transparent"
                                              : (darkMode?"rgba(255,255,255,.02)":"#FAFBFD"), // indented supplier row
                                    borderLeft: !isFirstInGroup ? `3px solid ${darkMode?"rgba(200,164,74,.3)":"#E8D8A0"}` : "none",
                                    borderBottom: ai<group.length-1 && isTermExpanded ? `1px solid ${C.cardBord}` : "none",
                                    alignItems:"center",
                                    cursor: isChosen ? "default" : "pointer",
                                    transition:"background .12s",
                                    paddingLeft: !isFirstInGroup ? 22 : 10,
                                  }}
                                  onMouseEnter={e=>{ if (!isChosen) e.currentTarget.style.background = darkMode ? "rgba(200,164,74,.06)" : "#FFFDF5"; }}
                                  onMouseLeave={e=>{
                                    e.currentTarget.style.background = isChosen ? (darkMode?"rgba(13,148,136,.10)":"#F0FDFA")
                                                                        : isAlgoPick ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4")
                                                                        : isFirstInGroup ? "transparent"
                                                                        : (darkMode?"rgba(255,255,255,.02)":"#FAFBFD");
                                  }}>
                                  <div style={{fontWeight:800, color: isAlgoPick ? savingsGreen : C.textMut, fontFamily:"Arial,sans-serif"}}>
                                    {isFirstInGroup ? `#${gi+1}` : ""}
                                  </div>
                                  <div style={{display:"flex", alignItems:"center", gap:5, fontWeight:600, color:C.textPri, fontFamily:FONT, flexWrap:"wrap", minWidth:0}}>
                                    {isFirstInGroup && group.length > 1 && (
                                      <span
                                        onClick={(e)=>{ e.stopPropagation(); setExpandedTerminals(et => ({...et, [`${r.id}:${termId}`]: !isTermExpanded})); }}
                                        style={{display:"inline-block", width:14, textAlign:"center", color:C.textMut, cursor:"pointer", userSelect:"none"}}
                                        title={isTermExpanded ? "Collapse suppliers" : `Show ${group.length-1} more supplier${group.length>2?"s":""}`}>
                                        {isTermExpanded ? "▾" : "▸"}
                                      </span>
                                    )}
                                    {isFirstInGroup
                                      ? <span>{alt.terminal.short} · {alt.terminal.name.split(",")[0]}</span>
                                      : <span style={{fontSize:9.5, color:C.textMut, fontWeight:500}}>↳ alt</span>
                                    }
                                    {(() => {
                                      const brand = supplierBrand(alt.supplier.name);
                                      return (
                                        <span style={{
                                          display:"inline-flex", alignItems:"center", gap:4,
                                          fontSize:9, fontWeight:800,
                                          color: brand.primary,
                                          background: `${brand.primary}20`,
                                          padding:"1px 5px 1px 2px", borderRadius:3, letterSpacing:.4,
                                          border:`1px solid ${brand.primary}50`,
                                        }}>
                                          <SupplierLogo supplierName={alt.supplier.name} supplierShort={alt.supplier.short} size={12}/>
                                          {alt.supplier.short}
                                          {alt.isSpot && <span style={{color:"#EA580C", fontWeight:800}}>·SPOT</span>}
                                          {!alt.isSpot && alt.contractStatus === "secondary" && <span style={{opacity:.75}}>·2°</span>}
                                        </span>
                                      );
                                    })()}
                                    {isChosen && (
                                      <span style={{fontSize:8, fontWeight:800, color:"#0D9488", background:darkMode?"rgba(13,148,136,.15)":"#CCFBF1", padding:"1px 5px", borderRadius:3, letterSpacing:.4, border:`1px solid ${darkMode?"rgba(13,148,136,.35)":"#99F6E4"}`}}>
                                        {r.isOverridden ? "YOUR PICK" : "PICK"}
                                      </span>
                                    )}
                                    {isAlgoPick && !isChosen && (
                                      <span style={{fontSize:8, fontWeight:800, color:savingsGreen, background:"rgba(22,163,74,.12)", padding:"1px 5px", borderRadius:3, letterSpacing:.4}}>OPTIMAL</span>
                                    )}
                                    {isAssigned && !isChosen && !isAlgoPick && (
                                      <span style={{fontSize:8, fontWeight:800, color:C.textMut, background:darkMode?"rgba(255,255,255,.06)":"#E5E9EF", padding:"1px 5px", borderRadius:3, letterSpacing:.4}}>ASSIGNED</span>
                                    )}
                                  </div>
                                  <div style={{textAlign:"right", color:milesColor, fontFamily:"Arial,sans-serif", fontWeight: altMiles > 120 ? 700 : 400}}>{altMiles.toFixed(0)}</div>
                                  <div style={{textAlign:"right", color:C.textSec, fontFamily:"Arial,sans-serif"}}>${alt.rack.toFixed(4)}</div>
                                  <div title={alt.isSpot ? `Spot premium $${alt.spotPremium.toFixed(4)}/gal (no contract)` : `Contract diff $${alt.diff.toFixed(4)}/gal`}
                                    style={{textAlign:"right", color: alt.isSpot ? "#EA580C" : C.textSec, fontFamily:"Arial,sans-serif", fontWeight: alt.isSpot ? 600 : 400}}>
                                    ${(alt.isSpot ? alt.spotPremium : alt.diff).toFixed(4)}
                                  </div>
                                  <div title={`Zone ${alt.freightZone?.id || 1} (${alt.freightZone?.label}) — base $${alt.freightBase?.toFixed(4)}/gal × ${alt.freightMult}× multiplier`}
                                    style={{textAlign:"right", color: alt.freightMult >= 1.9 ? "#EA580C" : alt.freightMult >= 1.4 ? "#F59E0B" : C.textSec, fontFamily:"Arial,sans-serif", fontWeight: alt.freightMult >= 1.4 ? 600 : 400}}>
                                    ${alt.freight.toFixed(4)}
                                  </div>
                                  <div style={{textAlign:"right", fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif"}}>${alt.landed.toFixed(4)}</div>
                                  <div style={{textAlign:"right", fontFamily:"Arial,sans-serif", color: deltaFromBest === 0 ? savingsGreen : C.textMut, fontWeight: deltaFromBest === 0 ? 700 : 400}}>
                                    {deltaFromBest === 0 ? "best" : `+$${deltaFromBest.toFixed(4)}`}
                                  </div>
                                  <div style={{textAlign:"center"}}>
                                    {isChosen ? (
                                      <span style={{fontSize:9, color:C.textMut, fontStyle:"italic"}}>selected</span>
                                    ) : (
                                      <span style={{
                                        fontSize:9.5, fontWeight:700, color:"#0D9488",
                                        padding:"2px 8px", borderRadius:4,
                                        background:darkMode?"rgba(13,148,136,.10)":"#F0FDFA",
                                        border:`1px solid ${darkMode?"rgba(13,148,136,.35)":"#99F6E4"}`,
                                      }}>
                                        Use →
                                      </span>
                                    )}
                                  </div>
                                </div>
                              );
                            })}
                          </div>
                        );
                      });
                    })()}
                  </div>

                  {/* Action */}
                  <div style={{display:"flex", gap:8, marginTop:12, flexWrap:"wrap"}}>
                    <button onClick={()=>onOpenDispatch(r)}
                      style={{
                        padding:"7px 14px", borderRadius:7, border:"none",
                        background:C.gold, color:"#0D1B2A",
                        fontSize:11, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                      }}>
                      Dispatch this load →
                    </button>
                    {r.isOverridden && (
                      <button onClick={()=>clearOverride(r.id)}
                        style={{
                          padding:"7px 14px", borderRadius:7,
                          border:`1px solid ${darkMode?"rgba(22,163,74,.45)":"#86EFAC"}`,
                          background: darkMode?"rgba(22,163,74,.08)":"#F0FDF4",
                          color:savingsGreen, fontSize:11, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                        }}>
                        ↺ Reset to optimal ({r.algoPick.terminal.short}/{r.algoPick.supplier.short})
                      </button>
                    )}
                    <button onClick={()=>setExpandedId(null)}
                      style={{
                        padding:"7px 14px", borderRadius:7,
                        border:`1px solid ${C.cardBord}`, background:"transparent",
                        color:C.textSec, fontSize:11, cursor:"pointer", fontFamily:FONT,
                      }}>
                      Close
                    </button>
                  </div>
                </div>
              )}
            </div>
          );
        })}
      </div>
      )}

      {/* ─── Trips view (consolidated multi-stop) ───────────────────── */}
      {viewMode === "trips" && (
      <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden"}}>
        {/* Trip column headers */}
        <div style={{
          display:"grid", gridTemplateColumns:"60px 90px 1fr 110px 90px 80px 100px 110px 30px",
          gap:8, padding:"10px 14px",
          background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
          borderBottom:`1px solid ${C.cardBord}`,
          fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase",
          fontFamily:FONT,
        }}>
          <div>Trip</div>
          <div>Terminal</div>
          <div>Stops</div>
          <div>Carrier</div>
          <div style={{textAlign:"right"}}>Volume</div>
          <div style={{textAlign:"right"}}>Miles</div>
          <div style={{textAlign:"right"}}>Trip cost</div>
          <div style={{textAlign:"right"}}>Saves</div>
          <div/>
        </div>

        {plan.trips.length === 0 ? (
          <div style={{padding:"40px 20px", textAlign:"center", color:C.textMut, fontSize:12, fontFamily:FONT}}>
            No trips planned. Add stores to the dispatch queue to generate trips.
          </div>
        ) : plan.trips.map((trip, i) => {
          const isOpen = expandedId === trip.id;
          const stopCount = trip.stops.length;
          const slackColor = trip.slackPct > 0.30 ? "#EA580C" : trip.slackPct > 0.15 ? "#F59E0B" : "#16A34A";
          return (
            <div key={trip.id} style={{borderBottom: i < plan.trips.length - 1 ? `1px solid ${C.cardBord}` : "none"}}>
              {/* Main trip row */}
              <div onClick={()=>setExpandedId(isOpen ? null : trip.id)}
                style={{
                  display:"grid", gridTemplateColumns:"60px 90px 1fr 110px 90px 80px 100px 110px 30px",
                  gap:8, padding:"12px 14px", alignItems:"center",
                  cursor:"pointer", transition:"background .12s",
                  background: isOpen ? (darkMode?"rgba(200,164,74,.06)":"#F8FAFB") : "transparent",
                }}
                onMouseEnter={e=>{ if (!isOpen) e.currentTarget.style.background = darkMode?"rgba(255,255,255,.02)":"#FAFBFD"; }}
                onMouseLeave={e=>{ if (!isOpen) e.currentTarget.style.background = "transparent"; }}>
                {/* Trip ID */}
                <div>
                  <div style={{fontSize:11.5, fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                    {trip.id}
                  </div>
                  {trip.isMultiStop && (
                    <div style={{
                      fontSize:8.5, fontWeight:800, color:"#16A34A",
                      background:darkMode?"rgba(22,163,74,.12)":"#F0FDF4",
                      padding:"1px 5px", borderRadius:3, marginTop:2, display:"inline-block",
                      letterSpacing:.4, border:"1px solid rgba(22,163,74,.3)",
                    }}>{stopCount}-STOP</div>
                  )}
                </div>
                {/* Terminal */}
                <div>
                  <div style={{fontSize:11.5, fontWeight:700, color:C.gold, fontFamily:"Arial,sans-serif"}}>
                    {trip.terminal.short}
                  </div>
                  <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>
                    {trip.terminal.name.split(",")[0]}
                  </div>
                </div>
                {/* Stops list (truncated) */}
                <div style={{minWidth:0, overflow:"hidden"}}>
                  <div style={{fontSize:11, color:C.textPri, fontFamily:FONT, fontWeight:600,
                    overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                    {trip.stops.map((s,si)=>(
                      <React.Fragment key={si}>
                        {si > 0 && <span style={{color:C.gold, margin:"0 6px", fontWeight:800}}>→</span>}
                        <span>{s.store.name}</span>
                      </React.Fragment>
                    ))}
                  </div>
                  <div style={{fontSize:9.5, color:C.textMut, marginTop:2,
                    overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                    {trip.stops.map(s => `${s.grade.charAt(0)}·${(s.vol/1000).toFixed(0)}K`).join(" / ")}
                    {trip.slack > 0 && (
                      <span style={{color:slackColor, marginLeft:8, fontWeight:600}}>
                        {(trip.slackPct*100).toFixed(0)}% slack ({(trip.slack/1000).toFixed(1)}K free)
                      </span>
                    )}
                  </div>
                </div>
                {/* Carrier */}
                <div style={{minWidth:0}}>
                  {trip.carrier ? (
                    <>
                      <div style={{fontSize:11, fontWeight:600, color:C.textPri, fontFamily:FONT,
                        overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                        {trip.carrier.short}
                      </div>
                      <div style={{fontSize:9.5, color:C.textMut}}>
                        {(trip.carrier.compartments||[]).join("/")} cap
                      </div>
                    </>
                  ) : (
                    <div style={{fontSize:10, color:"#EF4444", fontWeight:600}}>Unassigned</div>
                  )}
                </div>
                {/* Volume */}
                <div style={{textAlign:"right", fontSize:11, fontWeight:600, color:C.textPri, ...moneyStyle}}>
                  {(trip.totalGals/1000).toFixed(1)}K
                  <div style={{fontSize:9, fontWeight:400, color:C.textMut}}>gallons</div>
                </div>
                {/* Miles */}
                <div style={{textAlign:"right", fontSize:11, fontWeight:600, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                  {trip.mileage.toFixed(0)}
                  <div style={{fontSize:9, fontWeight:400, color:C.textMut}}>round-trip</div>
                </div>
                {/* Trip cost */}
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:11.5, ...moneyStyle, color:C.textPri}}>
                    ${Math.round(trip.tripCost).toLocaleString()}
                  </div>
                  <div style={{fontSize:9.5, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                    freight only
                  </div>
                </div>
                {/* Consolidation savings */}
                <div style={{textAlign:"right"}}>
                  <div style={{fontSize:12, ...moneyStyle, color: trip.savings > 0 ? "#16A34A" : C.textMut}}>
                    {trip.savings > 0 ? `+$${Math.round(trip.savings).toLocaleString()}` : "—"}
                  </div>
                  <div style={{fontSize:9, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                    {trip.savings > 0 ? "vs single-stops" : "single-stop"}
                  </div>
                </div>
                {/* Expand chevron */}
                <div style={{textAlign:"center", color:C.textMut, fontSize:11, fontFamily:"Arial,sans-serif"}}>
                  {isOpen ? "▾" : "▸"}
                </div>
              </div>

              {/* Expanded trip detail */}
              {isOpen && (
                <div style={{
                  padding:"14px 18px 16px 18px",
                  background:darkMode?"rgba(200,164,74,.04)":"#F8FAFB",
                  borderTop:`1px solid ${C.cardBord}`,
                }}>
                  {/* Compartment diagram */}
                  {trip.carrier && trip.compartments && (
                    <>
                      <div style={{fontSize:9.5, fontWeight:800, color:C.gold, letterSpacing:.8, textTransform:"uppercase", marginBottom:8}}>
                        Compartment loadout — {trip.carrier.short}
                      </div>
                      <div style={{display:"flex", gap:6, marginBottom:14}}>
                        {trip.compartments.map((comp, ci) => {
                          const fill = comp.fills[0];
                          const fillPct = comp.cap > 0 ? (fill ? fill.vol / comp.cap : 0) : 0;
                          const gradeColor = fill ? ({Regular:"#0891B2",Premium:"#0D9488",Diesel:"#EA580C"}[fill.grade] || C.textMut) : null;
                          return (
                            <div key={ci} style={{
                              flex:1, minWidth:0,
                              border:`1.5px solid ${fill ? gradeColor : C.cardBord}`,
                              borderRadius:6, overflow:"hidden",
                              background: darkMode ? "rgba(255,255,255,.02)" : "#fff",
                            }}>
                              <div style={{padding:"6px 10px", fontSize:9.5,
                                background: fill ? `${gradeColor}15` : "transparent",
                                borderBottom:`1px solid ${fill ? gradeColor : C.cardBord}40`,
                                display:"flex", justifyContent:"space-between", alignItems:"center",
                              }}>
                                <span style={{fontWeight:800, color:fill ? gradeColor : C.textMut, letterSpacing:.4}}>
                                  POCKET {ci+1}
                                </span>
                                <span style={{fontSize:9, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                                  {(comp.cap/1000).toFixed(0)}K cap
                                </span>
                              </div>
                              {/* Visual fill */}
                              <div style={{padding:"10px", minHeight:54}}>
                                {fill ? (
                                  <>
                                    <div style={{fontSize:10.5, fontWeight:700, color:C.textPri, fontFamily:FONT,
                                      overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap", marginBottom:3}}>
                                      {fill.store.name}
                                    </div>
                                    <div style={{fontSize:10, color:gradeColor, fontWeight:700, fontFamily:"Arial,sans-serif", marginBottom:5}}>
                                      {fill.grade} · {(fill.vol/1000).toFixed(1)}K gal
                                    </div>
                                    <div style={{height:6, background:darkMode?"rgba(255,255,255,.08)":"#E5E9EF", borderRadius:3, overflow:"hidden"}}>
                                      <div style={{height:"100%", width:`${fillPct*100}%`, background:gradeColor, borderRadius:3}}/>
                                    </div>
                                    <div style={{fontSize:9, color:C.textMut, marginTop:3, textAlign:"right", fontFamily:"Arial,sans-serif"}}>
                                      {(fillPct*100).toFixed(0)}% utilized
                                    </div>
                                  </>
                                ) : (
                                  <div style={{fontSize:10.5, color:C.textMut, fontStyle:"italic", textAlign:"center", paddingTop:10}}>
                                    Empty
                                    <div style={{fontSize:9, marginTop:3, opacity:.7}}>{(comp.cap/1000).toFixed(0)}K available</div>
                                  </div>
                                )}
                              </div>
                            </div>
                          );
                        })}
                      </div>
                    </>
                  )}

                  {/* Stop sequence */}
                  <div style={{fontSize:9.5, fontWeight:800, color:C.textMut, letterSpacing:.8, textTransform:"uppercase", marginBottom:6}}>
                    Stop sequence — nearest-neighbor route
                  </div>
                  <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:6, overflow:"hidden", marginBottom:12}}>
                    {/* Origin */}
                    <div style={{
                      display:"grid", gridTemplateColumns:"40px 1fr 80px 90px 90px",
                      gap:8, padding:"8px 12px", fontSize:10.5,
                      background:darkMode?"rgba(200,164,74,.10)":"#F8FAFB",
                      borderBottom:`1px solid ${C.cardBord}`,
                      alignItems:"center",
                    }}>
                      <div style={{fontWeight:800, color:C.gold, fontFamily:"Arial,sans-serif"}}>◆</div>
                      <div>
                        <div style={{fontWeight:700, color:C.textPri, fontFamily:FONT}}>
                          {trip.terminal.name} — load
                        </div>
                        <div style={{fontSize:9.5, color:C.textMut}}>Origin terminal</div>
                      </div>
                      <div/><div/><div/>
                    </div>
                    {/* Stops */}
                    {trip.stops.map((stop, si) => {
                      const prevLat = si === 0 ? trip.terminal.lat : trip.stops[si-1].store.lat;
                      const prevLng = si === 0 ? trip.terminal.lng : trip.stops[si-1].store.lng;
                      const legMiles = distMiles(prevLat, prevLng, stop.store.lat, stop.store.lng);
                      const gradeColor = {Regular:"#0891B2",Premium:"#0D9488",Diesel:"#EA580C"}[stop.grade] || C.textMut;
                      return (
                        <div key={si} style={{
                          display:"grid", gridTemplateColumns:"40px 1fr 80px 90px 90px",
                          gap:8, padding:"8px 12px", fontSize:10.5,
                          borderBottom: si < trip.stops.length - 1 ? `1px solid ${C.cardBord}` : "none",
                          alignItems:"center",
                        }}>
                          <div style={{
                            width:24, height:24, borderRadius:"50%",
                            background:gradeColor, color:"#fff",
                            display:"flex", alignItems:"center", justifyContent:"center",
                            fontSize:11, fontWeight:800, fontFamily:"Arial,sans-serif",
                          }}>{si+1}</div>
                          <div style={{minWidth:0}}>
                            <div style={{fontWeight:700, color:C.textPri, fontFamily:FONT,
                              overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                              {stop.store.name}
                            </div>
                            <div style={{fontSize:9.5, color:C.textMut}}>
                              {stop.store.city}, {stop.store.state} · runout in {stop.runoutLabel}
                            </div>
                          </div>
                          <div style={{textAlign:"right", color:gradeColor, fontWeight:700, fontFamily:FONT}}>
                            {stop.grade}
                          </div>
                          <div style={{textAlign:"right", fontFamily:"Arial,sans-serif", fontWeight:700, color:C.textPri}}>
                            {(stop.vol/1000).toFixed(1)}K gal
                          </div>
                          <div style={{textAlign:"right", fontSize:9.5, color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                            +{legMiles.toFixed(0)} mi
                          </div>
                        </div>
                      );
                    })}
                  </div>

                  {/* Cost breakdown */}
                  <div style={{display:"grid", gridTemplateColumns:"1fr 1fr 1fr", gap:8, marginBottom:12}}>
                    <div style={{padding:"8px 12px", borderRadius:6,
                      background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC",
                      border:`1px solid ${C.cardBord}`}}>
                      <div style={{fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase", marginBottom:3}}>
                        If dispatched separately
                      </div>
                      <div style={{fontSize:13, ...moneyStyle, color:C.textSec}}>
                        ${Math.round(trip.baselineCost).toLocaleString()}
                      </div>
                      <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>
                        {trip.stops.length} round trips
                      </div>
                    </div>
                    <div style={{padding:"8px 12px", borderRadius:6,
                      background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC",
                      border:`1px solid ${C.cardBord}`}}>
                      <div style={{fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase", marginBottom:3}}>
                        Consolidated trip
                      </div>
                      <div style={{fontSize:13, ...moneyStyle, color:C.textPri}}>
                        ${Math.round(trip.tripCost).toLocaleString()}
                      </div>
                      <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>
                        1 truck · {trip.mileage.toFixed(0)} mi total
                      </div>
                    </div>
                    <div style={{padding:"8px 12px", borderRadius:6,
                      background:darkMode?"rgba(22,163,74,.10)":"#F0FDF4",
                      border:"1px solid rgba(22,163,74,.3)"}}>
                      <div style={{fontSize:8.5, fontWeight:800, color:"#16A34A", letterSpacing:.6, textTransform:"uppercase", marginBottom:3}}>
                        Consolidation saves
                      </div>
                      <div style={{fontSize:13, ...moneyStyle, color:"#16A34A"}}>
                        ${Math.round(trip.savings).toLocaleString()}
                      </div>
                      <div style={{fontSize:9.5, color:"#16A34A", marginTop:1, opacity:.85}}>
                        {trip.baselineCost > 0 ? `${(100*trip.savings/trip.baselineCost).toFixed(0)}% lower freight` : ""}
                      </div>
                    </div>
                  </div>

                  {/* Actions */}
                  <div style={{display:"flex", gap:8}}>
                    <button onClick={()=>{
                      // Dispatch the FIRST stop using the optimizer's existing handler;
                      // for a real multi-stop trip you'd POST the whole trip object to the TMS.
                      const lead = trip.stops[0];
                      onOpenDispatch(lead);
                    }}
                      style={{
                        padding:"7px 14px", borderRadius:7, border:"none",
                        background:C.gold, color:"#0D1B2A",
                        fontSize:11, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                      }}>
                      Dispatch trip {trip.id} →
                    </button>
                    <button onClick={()=>setExpandedId(null)}
                      style={{
                        padding:"7px 14px", borderRadius:7,
                        border:`1px solid ${C.cardBord}`, background:"transparent",
                        color:C.textSec, fontSize:11, cursor:"pointer", fontFamily:FONT,
                      }}>
                      Close
                    </button>
                  </div>
                </div>
              )}
            </div>
          );
        })}
      </div>
      )}

      {/* ─── Methodology footer ────────────────────────────────────────── */}
      <div style={{
        padding:"10px 14px", borderRadius:8,
        background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
        border:`1px solid ${C.cardBord}`,
        fontSize:10.5, color:C.textSec, fontFamily:FONT, lineHeight:1.5,
      }}>
        <div>
          <span style={{fontWeight:800, color:C.textPri, letterSpacing:.5}}>Sourcing</span>
          <span style={{opacity:.7, marginLeft:6}}>
            Greedy per-load: for each store below reorder threshold, selects the lowest-landed terminal
            (rack + contract diff + <strong>distance-tiered freight</strong> + tax). Freight uses a four-zone model
            (0–25 / 25–50 / 50–100 / 100+ mi) at multipliers of 1.00× / 1.40× / 1.90× / 2.60× the
            base lane rate — matches the standard zoned-contract structure used by most c-store carriers.
            When <em>Territories: respected</em> is on (default), each load stays within its assigned
            terminal's Voronoi zone — savings come purely from multi-stop consolidation. Toggle to
            <em> crossing allowed</em> and the algorithm picks across all terminals; long-haul savings
            from rack price differences are now properly netted against zone-3/4 freight surcharges.
          </span>
        </div>
        <div style={{marginTop:6}}>
          <span style={{fontWeight:800, color:C.textPri, letterSpacing:.5}}>Trip consolidation</span>
          <span style={{opacity:.7, marginLeft:6}}>
            Bin-packing is NP-hard, so trips view uses first-fit-decreasing (FFD) on compartments —
            within ~22% of optimal in the worst case, near-optimal in practice. Stops within
            {" "}{MAX_CLUSTER_RADIUS_MI} mi of each other are eligible to share a truck. One product
            per compartment to avoid contamination. Consolidation savings = freight cost of running
            each stop as a solo round-trip minus the consolidated multi-stop trip cost.
          </span>
        </div>
      </div>

      {/* ─── Publish Day confirmation modal ──────────────────────────── */}
      {showPublishModal && (() => {
        const assignments = buildAssignments(plan.trips);
        const assignedCount = Object.keys(assignments).length;
        const unassignedCount = plan.trips.length - assignedCount;
        const totalGals = plan.trips.reduce((s,t) => s + t.totalGals, 0);
        const totalMiles = plan.trips.reduce((s,t) => s + t.mileage, 0);
        const totalSavings = plan.totalSavings + plan.tripSavings;
        return (
          <div
            onClick={()=>setShowPublishModal(false)}
            style={{
              position:"fixed", inset:0, zIndex:9999,
              background:"rgba(8,15,26,.65)", backdropFilter:"blur(3px)",
              display:"flex", alignItems:"center", justifyContent:"center",
              padding:20,
            }}>
            <div onClick={e=>e.stopPropagation()}
              style={{
                width:"min(720px, 100%)", maxHeight:"85vh", overflowY:"auto",
                background:C.cardBg, borderRadius:12,
                border:`1px solid ${C.cardBord}`,
                boxShadow:"0 20px 60px rgba(0,0,0,.4)",
                fontFamily:FONT,
              }}>
              {/* Header */}
              <div style={{
                padding:"16px 22px",
                background:"#0D1B2A",
                color:"#fff",
                display:"flex", alignItems:"center", justifyContent:"space-between",
                borderRadius:"12px 12px 0 0",
              }}>
                <div>
                  <div style={{fontSize:11, fontWeight:800, letterSpacing:1.2, textTransform:"uppercase", opacity:.9}}>
                    Confirm publish to schedule
                  </div>
                  <div style={{fontSize:18, fontWeight:800, marginTop:2}}>
                    Optimize Day — {plan.trips.length} trip{plan.trips.length!==1?"s":""}
                  </div>
                </div>
                <button onClick={()=>setShowPublishModal(false)}
                  style={{
                    width:32, height:32, borderRadius:"50%", border:"none",
                    background:"rgba(255,255,255,.18)", color:"#fff",
                    fontSize:18, cursor:"pointer", lineHeight:1,
                  }}>×</button>
              </div>

              {/* Body */}
              <div style={{padding:"18px 22px"}}>
                {/* Top stats — what publishing will do */}
                <div style={{display:"grid", gridTemplateColumns:"repeat(4, 1fr)", gap:8, marginBottom:18}}>
                  {[
                    { l:"Trips", v:plan.trips.length, sub:`${plan.consolidatedTrips} multi-stop` },
                    { l:"Drivers used", v:assignedCount, sub:`of ${plan.trips.length} trips` },
                    { l:"Gallons moved", v:`${(totalGals/1000).toFixed(0)}K`, sub:`${totalMiles.toFixed(0)} mi total` },
                    { l:"Total savings", v:`$${Math.round(totalSavings).toLocaleString()}`, sub:"sourcing + consolidation", color:"#16A34A" },
                  ].map((s,i)=>(
                    <div key={i} style={{
                      padding:"10px 12px", borderRadius:8,
                      border:`1px solid ${C.cardBord}`,
                      background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                    }}>
                      <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase", marginBottom:3}}>
                        {s.l}
                      </div>
                      <div style={{fontSize:18, fontWeight:800, color: s.color || C.textPri, fontFamily:"Arial,sans-serif"}}>
                        {s.v}
                      </div>
                      <div style={{fontSize:9.5, color:C.textMut, marginTop:1}}>{s.sub}</div>
                    </div>
                  ))}
                </div>

                {/* Warning if any unassignable */}
                {unassignedCount > 0 && (
                  <div style={{
                    padding:"10px 14px", borderRadius:7, marginBottom:14,
                    background: darkMode?"rgba(245,158,11,.10)":"#F8FAFB",
                    border:"1px solid rgba(245,158,11,.4)",
                    fontSize:11, color: darkMode?"#FCD34D":"#92400E",
                  }}>
                    <strong>{unassignedCount} trip{unassignedCount!==1?"s":""} couldn't be assigned</strong> — no
                    available driver from a carrier with terminal access. They'll stay in the Plan tab so
                    you can dispatch manually or wait for a driver to become available.
                  </div>
                )}

                {/* Per-trip assignment preview */}
                <div style={{fontSize:9.5, fontWeight:800, color:C.textMut, letterSpacing:.6, textTransform:"uppercase", marginBottom:6}}>
                  Driver assignments ({assignedCount} of {plan.trips.length})
                </div>
                <div style={{
                  border:`1px solid ${C.cardBord}`, borderRadius:7, overflow:"hidden",
                  maxHeight:240, overflowY:"auto",
                }}>
                  {plan.trips.map((trip, i) => {
                    const a = assignments[trip.id];
                    return (
                      <div key={trip.id} style={{
                        display:"grid", gridTemplateColumns:"60px 70px 1fr 1.2fr 70px",
                        gap:8, padding:"8px 12px", fontSize:10.5,
                        borderBottom: i < plan.trips.length-1 ? `1px solid ${C.cardBord}` : "none",
                        alignItems:"center",
                        background: !a ? (darkMode?"rgba(245,158,11,.06)":"#F8FAFB") : "transparent",
                      }}>
                        <div style={{fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                          {trip.id}
                        </div>
                        <div style={{fontWeight:700, color:C.gold, fontFamily:"Arial,sans-serif"}}>
                          {trip.terminal.short}
                        </div>
                        <div style={{minWidth:0, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap", color:C.textSec}}>
                          {trip.stops.length === 1
                            ? trip.stops[0].store.name
                            : `${trip.stops.length} stops · ${trip.stops.map(s=>s.store.name.split(" ")[0]).join(", ")}`}
                        </div>
                        <div style={{minWidth:0, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                          {a ? (
                            <span>
                              <strong style={{color:C.textPri}}>{a.tractor.driver}</strong>
                              <span style={{color:C.textMut}}> · {a.carrier.short} {a.tractor.unit}</span>
                            </span>
                          ) : (
                            <span style={{color:"#92400E", fontStyle:"italic"}}>no driver available</span>
                          )}
                        </div>
                        <div style={{textAlign:"right", color:C.textMut, fontFamily:"Arial,sans-serif"}}>
                          {a ? `${(a.tractor.hos||0).toFixed(1)}h HOS` : "—"}
                        </div>
                      </div>
                    );
                  })}
                </div>

                {/* What happens next */}
                <div style={{
                  marginTop:14, padding:"10px 14px", borderRadius:7,
                  background: darkMode?"rgba(8,145,178,.08)":"#ECFEFF",
                  border:"1px solid rgba(8,145,178,.3)",
                  fontSize:11, color: darkMode?"#67E8F9":"#155E75", lineHeight:1.5,
                }}>
                  <strong>What happens when you publish:</strong> All {assignedCount} assigned trips become SCHEDULED loads
                  in the live feed. They'll appear instantly on the Day Schedule Gantt and Today's Schedule on the
                  Command Center. In production this would also POST each load to your TMS and notify drivers.
                </div>
              </div>

              {/* Footer actions */}
              <div style={{
                padding:"14px 22px", borderTop:`1px solid ${C.cardBord}`,
                display:"flex", justifyContent:"flex-end", gap:8,
                background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                borderRadius:"0 0 12px 12px",
              }}>
                <button onClick={()=>setShowPublishModal(false)}
                  style={{
                    padding:"9px 18px", borderRadius:7,
                    border:`1px solid ${C.cardBord}`, background:"transparent",
                    color:C.textSec, fontSize:12, fontWeight:600, cursor:"pointer", fontFamily:FONT,
                  }}>
                  Cancel
                </button>
                <button
                  onClick={()=>{
                    setShowPublishModal(false);
                    onPublishDay && onPublishDay(plan.trips, assignments);
                  }}
                  disabled={assignedCount === 0}
                  style={{
                    padding:"9px 22px", borderRadius:7, border:"none",
                    background: assignedCount === 0
                      ? (darkMode?"rgba(255,255,255,.08)":"#E5E9EF")
                      : "#0D1B2A",
                    color: assignedCount === 0 ? C.textMut : "#fff",
                    fontSize:12, fontWeight:800, letterSpacing:.3,
                    cursor: assignedCount === 0 ? "not-allowed" : "pointer", fontFamily:FONT,
                    boxShadow: assignedCount === 0 ? "none" : "0 2px 8px rgba(200,164,74,.45)",
                  }}>
                  Publish {assignedCount} trip{assignedCount!==1?"s":""} to schedule
                </button>
              </div>
            </div>
          </div>
        );
      })()}
    </div>
  );
}


// ─── TodaysSchedule — Command Center "what's already in motion" panel ───────
// Replaces the mini-map on the Command Center. Shows every load currently
// loading / en route / delivering, sorted by ETA (soonest first), with status
// chips and a progress bar per row. Rows are clickable — clicking jumps to
// the Dispatch tab with that load pre-selected.
function TodaysSchedule({ loads, onJumpToDispatch, onSelectLoad, darkMode, C, FONT }) {
  const [statusFilter, setStatusFilter] = useState("ALL");

  const STATUS_META = {
    LOADING:     { color:"#F59E0B", bg:"#F8FAFB", darkBg:"rgba(245,158,11,.12)",  icon:"●", label:"Loading" },
    "EN ROUTE":  { color:"#0891B2", bg:"#ECFEFF", darkBg:"rgba(8,145,178,.12)",   icon:"→", label:"En Route" },
    DELIVERING:  { color:"#22C55E", bg:"#F0FDF4", darkBg:"rgba(34,197,94,.12)",   icon:"▼", label:"Delivering" },
  };
  const STATUSES = ["LOADING","EN ROUTE","DELIVERING"];

  const filtered = useMemo(()=>{
    let arr = loads.filter(l => STATUSES.includes(l.status));
    if (statusFilter !== "ALL") arr = arr.filter(l => l.status === statusFilter);
    // Sort by ETA ascending — soonest arrivals at top
    return arr.slice().sort((a,b) => (a.eta||"99:99").localeCompare(b.eta||"99:99"));
  }, [loads, statusFilter]);

  const counts = STATUSES.reduce((acc,s)=>{ acc[s] = loads.filter(l=>l.status===s).length; return acc; }, {});
  const totalActive = counts.LOADING + counts["EN ROUTE"] + counts.DELIVERING;

  return (
    <div style={{
      background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10,
      overflow:"hidden", flex:1, display:"flex", flexDirection:"column", minHeight:400,
    }}>
      {/* Header */}
      <div style={{
        padding:"12px 16px", borderBottom:`1px solid ${C.cardBord}`,
        display:"flex", alignItems:"center", justifyContent:"space-between", flexShrink:0,
      }}>
        <div>
          <div style={{fontSize:13, fontWeight:700, color:C.textPri, fontFamily:FONT}}>Today's Schedule</div>
          <div style={{fontSize:10.5, color:C.textSec, marginTop:1}}>
            {totalActive} load{totalActive!==1?"s":""} in motion · sorted by ETA
          </div>
        </div>
        <button onClick={onJumpToDispatch}
          style={{
            padding:"5px 12px", borderRadius:6,
            border:`1px solid ${C.cardBord}`, background:"transparent",
            color:C.gold, fontSize:11, fontWeight:700, cursor:"pointer", fontFamily:FONT,
          }}>
          Open Dispatch →
        </button>
      </div>

      {/* Status filter chips */}
      <div style={{
        display:"flex", gap:5, padding:"8px 12px",
        borderBottom:`1px solid ${C.cardBord}`, flexWrap:"wrap", flexShrink:0,
      }}>
        {[
          { f:"ALL", l:"All", c:C.textSec, n:totalActive },
          ...STATUSES.map(s => ({ f:s, l:STATUS_META[s].label, c:STATUS_META[s].color, n:counts[s] })),
        ].map(chip => {
          const on = statusFilter===chip.f;
          return (
            <button key={chip.f} onClick={()=>setStatusFilter(chip.f)}
              style={{
                padding:"2px 9px", borderRadius:10,
                border:`1.5px solid ${on?chip.c:C.cardBord}`,
                background:on?`${chip.c}22`:"transparent",
                color:on?chip.c:C.textSec,
                fontSize:9.5, fontWeight:on?700:400,
                cursor:"pointer", fontFamily:FONT, whiteSpace:"nowrap",
              }}>
              {chip.l} {chip.n>0 && `(${chip.n})`}
            </button>
          );
        })}
      </div>

      {/* Scrollable load list */}
      <div style={{overflowY:"auto", flex:1}}>
        {filtered.length===0 ? (
          <div style={{padding:"32px 16px", textAlign:"center", color:C.textMut, fontSize:11, fontFamily:FONT}}>
            {statusFilter==="ALL" ? "No active loads" : `No loads ${STATUS_META[statusFilter]?.label.toLowerCase()}`}
          </div>
        ) : filtered.map(ld => {
          const meta = STATUS_META[ld.status] || STATUS_META.LOADING;
          const detained = (ld.detained||0) > 15;
          return (
            <div key={ld.id} onClick={()=>onSelectLoad(ld)}
              style={{
                padding:"10px 14px", borderBottom:`1px solid ${C.cardBord}`,
                display:"flex", gap:10, alignItems:"flex-start", cursor:"pointer",
                background: darkMode ? "transparent" : "transparent",
                transition:"background .12s",
              }}
              onMouseEnter={e=>{e.currentTarget.style.background = darkMode ? "rgba(200,164,74,.04)" : "#FAFBFD";}}
              onMouseLeave={e=>{e.currentTarget.style.background = "transparent";}}>
              {/* Left: colored status spine + icon */}
              <div style={{width:3, borderRadius:2, background:meta.color, flexShrink:0, alignSelf:"stretch", minHeight:44}}/>
              {/* Middle: details */}
              <div style={{flex:1, minWidth:0}}>
                <div style={{display:"flex", alignItems:"center", gap:7, marginBottom:3, flexWrap:"wrap"}}>
                  <span style={{
                    fontSize:8.5, fontWeight:800, padding:"2px 6px", borderRadius:4,
                    background:`${meta.color}22`, color:meta.color,
                    letterSpacing:.4, textTransform:"uppercase", flexShrink:0,
                    border:`1px solid ${meta.color}30`,
                  }}>{ld.status}</span>
                  <span style={{fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT}}>
                    ETA {ld.eta}
                  </span>
                  {detained && (
                    <span style={{fontSize:8.5, fontWeight:700, color:"#DC2626", background:"#FEE2E2", padding:"1px 5px", borderRadius:3, fontFamily:FONT}}>
                      detained {ld.detained}min
                    </span>
                  )}
                </div>
                <div style={{fontSize:10.5, color:C.textSec, marginBottom:2, fontFamily:FONT}}>
                  <span style={{fontWeight:600, color:C.textPri}}>{ld.carrier} {ld.truck}</span>
                  <span style={{opacity:.7}}> · {ld.driver}</span>
                </div>
                <div style={{fontSize:10, color:C.textMut, marginBottom:5, fontFamily:FONT, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap"}}>
                  {ld.origin.split(",")[0]} <span style={{color:meta.color, fontWeight:700}}>→</span> {ld.dest}
                  <span style={{opacity:.75, marginLeft:6}}>{(ld.gals/1000).toFixed(0)}K gal {ld.grade}</span>
                </div>
                {/* Progress bar */}
                <div style={{display:"flex", alignItems:"center", gap:8}}>
                  <div style={{flex:1, height:5, background:darkMode?"rgba(255,255,255,.06)":"#E5E9EF", borderRadius:3, overflow:"hidden"}}>
                    <div style={{
                      height:"100%", width:`${ld.pct}%`,
                      background:meta.color, borderRadius:3,
                      transition:"width .4s ease",
                    }}/>
                  </div>
                  <span style={{fontSize:9.5, fontWeight:700, color:meta.color, fontFamily:"Arial,sans-serif", minWidth:28, textAlign:"right"}}>
                    {ld.pct}%
                  </span>
                </div>
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );
}


// ─── AttentionBar — Command-Center-only "today's priority" one-liner ─────────
// Resolves to a single call-to-action sentence based on live state. Makes the
// daily question ("where do I start today?") obvious at a glance.
function AttentionBar({ critical, urgent, reorder, alerts, availTrucks, onDispatch, onViewAlerts, darkMode }) {
  const FONT = "Arial,sans-serif";
  // Pick the single message that best summarises the moment
  let message, cta, ctaLabel, color, icon;
  if (critical.length > 0) {
    message = `${critical.length} store${critical.length>1?"s":""} need${critical.length>1?"":"s"} fuel today.`;
    cta = onDispatch; ctaLabel = "Open dispatch";
    color = "#EF4444"; icon = "●";
  } else if (urgent.length > 0) {
    message = `${urgent.length} store${urgent.length>1?"s":""} will be critical within 36 hours.`;
    cta = onViewAlerts; ctaLabel = "Review alerts";
    color = "#F59E0B"; icon = "▲";
  } else if (alerts.filter(a=>a.level==="DEADLINE").length > 0) {
    const d = alerts.filter(a=>a.level==="DEADLINE").length;
    message = `${d} nomination deadline${d>1?"s":""} today.`;
    cta = onViewAlerts; ctaLabel = "Review deadlines";
    color = "#EA580C"; icon = "";
  } else if (reorder.length > 0) {
    message = `${reorder.length} store${reorder.length>1?"s":""} queued for reorder within 3 days — plan now.`;
    cta = onViewAlerts; ctaLabel = "See queue";
    color = "#F4D398"; icon = "○";
  } else {
    message = "All systems normal. No critical replenishment or deadlines today.";
    cta = null; ctaLabel = null;
    color = "#22C55E"; icon = "";
  }
  return (
    <div style={{
      display:"flex", alignItems:"center", gap:14,
      padding:"12px 18px", borderRadius:10,
      background: darkMode ? "rgba(13,22,39,.55)" : "#fff",
      border: `1px solid ${color}40`,
      borderLeft: `4px solid ${color}`,
      boxShadow: darkMode ? "none" : "0 1px 3px rgba(13,22,40,.06)",
      fontFamily: FONT,
    }}>
      <div style={{
        width:28, height:28, borderRadius:"50%",
        background: `${color}18`, color,
        display:"flex", alignItems:"center", justifyContent:"center",
        fontSize:14, fontWeight:800, flexShrink:0,
      }}>{icon}</div>
      <div style={{ flex:1, minWidth:0 }}>
        <div style={{ fontSize:9.5, fontWeight:800, color, letterSpacing:.7, textTransform:"uppercase", marginBottom:2 }}>
          Today's priority
        </div>
        <div style={{ fontSize:13.5, fontWeight:600, color: darkMode ? "#E8EDF6" : "#0D1B2A" }}>
          {message}
        </div>
      </div>
      {cta && (
        <button onClick={cta}
          style={{
            padding:"7px 14px", borderRadius:7, border:"none",
            background: color, color:"#fff",
            fontSize:11.5, fontWeight:700, cursor:"pointer",
            fontFamily: FONT, whiteSpace:"nowrap", flexShrink:0,
            boxShadow: `0 2px 6px ${color}55`,
          }}>
          {ctaLabel} →
        </button>
      )}
    </div>
  );
}


// ─── TourOverlay — guided walkthrough for demos ─────────────────────────────
// Renders a dim backdrop with a "spotlight" cutout over the currently-active
// step's target element, plus a tooltip card with the step caption, progress,
// and Prev/Next/Skip controls. Steps can optionally switch tabs via setActiveTab
// so the user watches the app navigate itself.
const TOUR_STEPS = [
  {
    title: "Welcome",
    body: "This is the FuelRun procurement platform. We'll spend about a minute walking through where everything lives — you can skip any time.",
    targetSelector: null, // centered modal
    tab: "command",
  },
  {
    title: "Start your day here",
    body: "Command Center answers 'what needs fuel today'. The bar at the top pulls out the single most important thing. Below that are your six daily KPIs.",
    targetSelector: "[data-tour='attention-bar']",
    tab: "command",
    placement: "bottom",
  },
  {
    title: "Active alerts feed",
    body: "Every critical, urgent, and pipeline event lands here, sorted by priority. Click Dispatch on any red alert to launch a truck in two clicks.",
    targetSelector: "[data-tour='alert-feed']",
    tab: "command",
    placement: "right",
  },
  {
    title: "Today's schedule",
    body: "Every load already in motion — loading at the rack, en route, or delivering — sorted by ETA. Click any row to open the load in Dispatch.",
    targetSelector: "[data-tour='command-schedule']",
    tab: "command",
    placement: "left",
  },
  {
    title: "The Plan tab does the math for you",
    body: "Every morning this page computes the cheapest terminal for each dispatch using live rack prices, freight, and contract differentials, and shows the projected savings vs. using your assigned terminals naively.",
    targetSelector: "[data-tour='plan']",
    tab: "plan",
    placement: "bottom",
  },
  {
    title: "Full store map",
    body: "Here's the full version with service territories, real pipeline routes, and zoomable pan & zoom. Toggle 'Territories' to see which terminal feeds which stores.",
    targetSelector: "[data-tour='replenmap']",
    tab: "replenmap",
    placement: "bottom",
  },
  {
    title: "Dispatch board",
    body: "Every carrier, truck, and driver lives here. The board updates as loads move from scheduled → loading → en route → delivered.",
    targetSelector: "[data-tour='dispatch']",
    tab: "dispatch",
    placement: "bottom",
  },
  {
    title: "Rack prices",
    body: "Real-time wholesale prices at every terminal, with freight added to show landed cost at your stores. Flip between contract and spot to compare.",
    targetSelector: "[data-tour='rack']",
    tab: "rack",
    placement: "bottom",
  },
  {
    title: "You're ready",
    body: "That's the tour. The sidebar always tells you what each page is for — the subtitle under each tab name describes the job. Happy hauling.",
    targetSelector: null,
    tab: "command",
  },
];

function TourOverlay({ step, setStep, setActiveTab, darkMode }) {
  const FONT = "Arial,sans-serif";
  const [rect, setRect] = useState(null);
  const current = TOUR_STEPS[step-1]; // step is 1-indexed; 0 means inactive

  // When the step changes, switch to the target tab then locate the target DOM node
  useEffect(()=>{
    if (!current) { setRect(null); return; }
    if (current.tab) setActiveTab(current.tab);
    // Small delay to let the tab render before measuring
    const t = setTimeout(()=>{
      if (!current.targetSelector) { setRect(null); return; }
      const el = document.querySelector(current.targetSelector);
      if (!el) { setRect(null); return; }
      const r = el.getBoundingClientRect();
      setRect({ x:r.left, y:r.top, w:r.width, h:r.height });
      // Scroll into view if needed
      if (r.top < 0 || r.bottom > window.innerHeight) {
        el.scrollIntoView({ behavior:"smooth", block:"center" });
      }
    }, 250);
    return ()=>clearTimeout(t);
  }, [step]);

  if (!current) return null;

  const total = TOUR_STEPS.length;
  const exit = ()=>setStep(0);

  // Tooltip positioning — centred if no target, otherwise relative to target rect
  const PAD = 14, TT_W = 340, TT_H = 180;
  let tipX, tipY;
  if (!rect) {
    tipX = window.innerWidth/2 - TT_W/2;
    tipY = window.innerHeight/2 - TT_H/2;
  } else {
    const placement = current.placement || "bottom";
    if (placement==="bottom") { tipX = rect.x + rect.w/2 - TT_W/2; tipY = rect.y + rect.h + PAD; }
    else if (placement==="top")    { tipX = rect.x + rect.w/2 - TT_W/2; tipY = rect.y - TT_H - PAD; }
    else if (placement==="right")  { tipX = rect.x + rect.w + PAD; tipY = rect.y + rect.h/2 - TT_H/2; }
    else if (placement==="left")   { tipX = rect.x - TT_W - PAD; tipY = rect.y + rect.h/2 - TT_H/2; }
    // Clamp to viewport
    tipX = Math.max(12, Math.min(window.innerWidth - TT_W - 12, tipX));
    tipY = Math.max(12, Math.min(window.innerHeight - TT_H - 12, tipY));
  }

  return (
    <div style={{ position:"fixed", inset:0, zIndex:2000, pointerEvents:"auto", fontFamily:FONT }}>
      {/* Dim backdrop with spotlight cutout via SVG mask */}
      <svg width="100%" height="100%" style={{ position:"absolute", inset:0, pointerEvents:"auto" }}
        onClick={exit}>
        <defs>
          <mask id="tourMask">
            <rect width="100%" height="100%" fill="#fff"/>
            {rect && (
              <rect x={rect.x-8} y={rect.y-8} width={rect.w+16} height={rect.h+16}
                rx={10} fill="#000"/>
            )}
          </mask>
        </defs>
        <rect width="100%" height="100%" fill="rgba(9,14,26,.72)" mask="url(#tourMask)"/>
        {rect && (
          <rect x={rect.x-8} y={rect.y-8} width={rect.w+16} height={rect.h+16}
            rx={10} fill="none" stroke="#F4D398" strokeWidth={2} strokeOpacity={0.85}
            style={{pointerEvents:"none"}}>
            <animate attributeName="stroke-opacity" values="0.85;0.4;0.85" dur="1.8s" repeatCount="indefinite"/>
          </rect>
        )}
      </svg>

      {/* Tooltip card */}
      <div onClick={e=>e.stopPropagation()}
        style={{
          position:"absolute", left:tipX, top:tipY, width:TT_W,
          background: darkMode ? "#0F1420" : "#fff",
          borderRadius:12, border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,
          boxShadow:"0 20px 60px rgba(0,0,0,.45)",
          padding:"16px 18px",
          color: darkMode ? "#E8EDF6" : "#0D1B2A",
        }}>
        <div style={{ display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:8 }}>
          <div style={{ fontSize:9.5, fontWeight:800, color:"#F4D398", letterSpacing:.7, textTransform:"uppercase" }}>
            Step {step} of {total}
          </div>
          <button onClick={exit} aria-label="close tour"
            style={{ border:"none", background:"transparent", color: darkMode?"#7B8FAF":"#4A5E7A",
              fontSize:16, cursor:"pointer", lineHeight:1, padding:0 }}>×</button>
        </div>
        <div style={{ fontSize:15, fontWeight:800, marginBottom:6 }}>{current.title}</div>
        <div style={{ fontSize:12.5, color: darkMode ? "#B7C7DC" : "#4A5E7A", lineHeight:1.5, marginBottom:14 }}>
          {current.body}
        </div>
        {/* Progress dots */}
        <div style={{ display:"flex", gap:4, marginBottom:14 }}>
          {TOUR_STEPS.map((_,i)=>(
            <div key={i} style={{
              flex:1, height:3, borderRadius:2,
              background: i < step ? "#F4D398" : (darkMode?"#1E2840":"#E2E8F0"),
            }}/>
          ))}
        </div>
        <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center" }}>
          <button onClick={exit}
            style={{ border:"none", background:"transparent", color: darkMode?"#7B8FAF":"#4A5E7A",
              fontSize:11, cursor:"pointer", fontFamily:FONT }}>
            Skip tour
          </button>
          <div style={{ display:"flex", gap:6 }}>
            {step > 1 && (
              <button onClick={()=>setStep(step-1)}
                style={{ padding:"6px 12px", borderRadius:6,
                  border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,
                  background:"transparent", color: darkMode?"#E8EDF6":"#0D1B2A",
                  fontSize:11.5, fontWeight:600, cursor:"pointer", fontFamily:FONT }}>
                Back
              </button>
            )}
            {step < total ? (
              <button onClick={()=>setStep(step+1)}
                style={{ padding:"6px 14px", borderRadius:6, border:"none",
                  background:"#F4D398", color:"#0D1B2A",
                  fontSize:11.5, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                  boxShadow:"0 2px 6px rgba(200,164,74,.4)" }}>
                Next →
              </button>
            ) : (
              <button onClick={exit}
                style={{ padding:"6px 14px", borderRadius:6, border:"none",
                  background:"#22C55E", color:"#fff",
                  fontSize:11.5, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                  boxShadow:"0 2px 6px rgba(34,197,94,.4)" }}>
                Got it
              </button>
            )}
          </div>
        </div>
      </div>
    </div>
  );
}


export default function FuelProcurementPlatform() {
  const [darkMode, setDarkMode] = useState(false);
  const [activeTab, setActiveTab] = useState("command");
  // ── Navigation & guidance state ──────────────────────────────────────────
  const [tourStep, setTourStep] = useState(0);       // 0 = off, 1..N = current step
  const [dispatchCrumb, setDispatchCrumb] = useState(null); // source-of-navigation hint
  const [tickerPos, setTickerPos] = useState(0);
  const [selectedTerminal, setSelectedTerminal] = useState("selma");
  const [selectedGrade, setSelectedGrade] = useState("Regular");
  const [selectedState, setSelectedState] = useState("ALL");
  const [orderSearch, setOrderSearch] = useState("");
  const [orderFilter, setOrderFilter] = useState("ALL");
  const [invSort, setInvSort] = useState("daysSupply");
  const [pricingState, setPricingState] = useState("ALL");
  const [sidebarExpanded, setSidebarExpanded] = useState(true);
  const [liftVol, setLiftVol] = useState(100000);
  const [dispatchTab, setDispatchTab] = useState("live");
  const [alertLevelFilter, setAlertLevelFilter] = useState("ALL");
  const [mapFilter, setMapFilter] = useState("ALL");
  const [mapGrade, setMapGrade] = useState("ALL");
  const [hoveredStore, setHoveredStore] = useState(null);
  const [selectedStore, setSelectedStore] = useState(null);
  const [procTab, setProcTab] = useState("suppliers");
  const [hoveredScoreId, setHoveredScoreId] = useState(null);
  const [pos, setPos] = useState(PURCHASE_ORDERS_DATA);
  const [alerts, setAlerts] = useState(PRICE_ALERTS_DATA);
  const [showPOModal, setShowPOModal] = useState(false);
  const [newPO, setNewPO] = useState({supplierId:"sup1",terminal:"selma",grade:"Regular",gals:50000,deliveryDate:"2025-04-19",notes:""});
  const [aiSourcingLoading, setAiSourcingLoading] = useState(false);
  const [aiSourcingResult, setAiSourcingResult] = useState(null);
  const [lcSupp, setLcSupp] = useState("sup1");
  const [lcTerm, setLcTerm] = useState("selma");
  const [lcGrade, setLcGrade] = useState("Regular");
  const [lcGals, setLcGals] = useState(100000);
  const [lcDelivState, setLcDelivState] = useState("NC");
  const [selectedLoad, setSelectedLoad] = useState(null);
  const [showAdvisor, setShowAdvisor] = useState(false);
  const [advisorLoading, setAdvisorLoading] = useState(false);
  const [advisorText, setAdvisorText] = useState("");
  const [disruptionDays, setDisruptionDays] = useState(3);
  const [disruptionTerminal, setDisruptionTerminal] = useState("selma");
  const [forecastTerminal, setForecastTerminal] = useState("selma");
  const [forecastGrade, setForecastGrade] = useState("Regular");
  // Contracts tab state
  const [contractFilter, setContractFilter] = useState("all"); // all | at-risk | on-pace | renewing
  const [contractSort, setContractSort] = useState("risk");    // risk | supplier | expiry | terminal
  const [expandedContract, setExpandedContract] = useState(null); // supplier id or null
  // planFilter: set when navigating to Plan tab with context from another screen.
  // Shape: { terminalId, grade?, supplierShort?, reason, message } | null
  // Cleared automatically when user leaves the Plan tab, or manually via the banner.
  const [planFilter, setPlanFilter] = useState(null);
  // Clear planFilter automatically when navigating away from the Plan tab, so
  // returning to Plan later via the sidebar shows the full unfiltered view.
  useEffect(() => {
    if (activeTab !== "plan" && planFilter !== null) {
      setPlanFilter(null);
    }
  }, [activeTab, planFilter]);
  // Today's Best Buy state — which cell is expanded to show full alternatives
  const [bestBuyExpanded, setBestBuyExpanded] = useState(null); // "terminalId:grade" or null
  const [bestBuyFilter, setBestBuyFilter] = useState("all"); // "all" | "contract" | "spot"
  // Strategy tab sub-tabs
  const [strategyTab, setStrategyTab] = useState("contractspot"); // contractspot | hedging | disruption
  // Contract/spot mix what-if slider — controls the projected contract share
  const [whatIfContractPct, setWhatIfContractPct] = useState(75); // 0-100
  // Lift-ahead optimizer — which terminal/grade the user is evaluating
  const [liftAheadTerminal, setLiftAheadTerminal] = useState("selma");
  const [liftAheadGrade, setLiftAheadGrade] = useState("Regular");
  const [liftAheadDays, setLiftAheadDays] = useState(14);
  // Strategy tab — contract vs spot controls
  const [mixSimContract, setMixSimContract] = useState(78);   // % contract in scenario
  const [strategyGrade, setStrategyGrade] = useState("Regular"); // chart focus
  const [weekOffset, setWeekOffset] = useState(0);
  const [toasts, setToasts] = useState([]);
  const [liveLoads, setLiveLoads] = useState(ACTIVE_LOADS);
  const [showDispatchModal, setShowDispatchModal] = useState(false);
  const [dispatchTarget, setDispatchTarget] = useState(null);
  const [dispatchCarrierId, setDispatchCarrierId] = useState(null);
  const [dispatchTruckId, setDispatchTruckId] = useState(null);
  const [scheduleDate, setScheduleDate] = useState("2025-04-18");
  const [scheduleTime, setScheduleTime] = useState("10:00");
  const [aiDispatchLoading, setAiDispatchLoading] = useState(false);
  const [aiDispatchResult, setAiDispatchResult] = useState(null);
  const [carrierFilter, setCarrierFilter] = useState("ALL");
  const [statusFilter, setStatusFilter] = useState("ALL");
  const [inboxRead, setInboxRead] = useState([]);

  const C = makeTheme(darkMode);
  const tickerRef = useRef(null);

  // Ticker scroll
  useEffect(() => {
    const interval = setInterval(() => {
      setTickerPos(p => p + 0.5);
    }, 20);
    return () => clearInterval(interval);
  }, []);

  //  Helpers 
  const addToast = React.useCallback((msg, type="success") => {
    const id = Date.now();
    setToasts(t=>[...t, {id, msg, type}]);
    setTimeout(()=>setToasts(t=>t.filter(x=>x.id!==id)), 3200);
  }, []);

  // Project HOS at a future scheduled time
  const projectHOS = (currentHOS, schedDate, schedTime) => {
    const todayMs  = new Date("2025-04-16T08:22:00").getTime();
    const schedMs  = new Date(schedDate + "T" + schedTime + ":00").getTime();
    const hoursAway = Math.max(0, (schedMs - todayMs) / 3600000);
    if (hoursAway >= 34) return 11;       // Full 34-hr DOT restart
    if (hoursAway >= 10) return 11;       // 10-hr rest reset
    return Math.max(0, +(currentHOS - hoursAway * 0.4).toFixed(1)); // partial draw-down
  };

  const hosLabel = (h) => h >= 8 ? "green" : h >= 4 ? "amber" : "red";
  const hosColor = (h, C) => h >= 8 ? C.green : h >= 4 ? C.amber : C.red;

  const runAIDispatch = async () => {
    if (!dispatchTarget) return;
    setAiDispatchLoading(true);
    setAiDispatchResult(null);
    try {
      const store      = STORES.find(s=>s.id===dispatchTarget.storeId);
      const terminal   = TERMINALS.find(t=>t.id===dispatchTarget.terminal);
      const depletion  = DEPLETION.find(d=>d.storeId===dispatchTarget.storeId);
      const termStatus = TERMINAL_STATUS[dispatchTarget.terminal||"selma"];
      const pipeWin    = COLONIAL.terminalWindows[dispatchTarget.terminal||"selma"];

      const availCarriers = CARRIER_FLEET.filter(c=>
        c.available>0 && c.terminalAccess.includes(dispatchTarget.terminal||"")
      ).map(c=>({
        id:c.id, name:c.name, short:c.short, rating:c.rating,
        ytdDetentionHrs:c.ytdDetentionHrs, ytdOverShort:c.ytdOverShort,
        rateBase:c.rateBase, ratePerMile:c.ratePerMile, detentionRate:c.detentionRate,
        hazmatCert:c.hazmatCert, vaporRecovery:c.vaporRecovery,
        trucks: c.tractors.filter(t=>t.status==="AVAILABLE").map(t=>({
          id:t.id, unit:t.unit, driver:t.driver,
          hosNow:t.hos, hosAtScheduled:projectHOS(t.hos,scheduleDate,scheduleTime),
          location:t.location, lastInspect:t.lastInspect,
          compartments:c.compartments,
          bestFit:Math.min(...c.compartments.map(cp=>Math.abs(cp-(dispatchTarget.vol||8000)))),
        })),
      }));

      const prompt = `You are a fuel dispatch optimizer for a 60-store c-store chain in NC, SC, VA, GA, FL. Be precise and data-driven.

LOAD:
- Store: ${store?.name||"Unknown"}, ${store?.state}
- Grade: ${dispatchTarget.grade} | Volume: ${(dispatchTarget.vol||0).toLocaleString()} gal
- Days to critical: ${depletion?.minCritical?.toFixed(1)||"?"} | Days to reorder: ${depletion?.minReorder?.toFixed(1)||"?"}
- Terminal: ${terminal?.name} (${terminal?.pipeline})
- Requested: ${scheduleDate} at ${scheduleTime}

TERMINAL:
- Rack wait: ${termStatus?.rackWait}min (${termStatus?.congestion}) | Lanes: ${termStatus?.lanesOpen}/${termStatus?.lanesTotal}
- Pipeline window: ${pipeWin?.daysToWindow===0?"OPEN NOW":"Opens in "+pipeWin?.daysToWindow+" days"}
- Colonial nomination deadline: ${COLONIAL.nominationDeadline}

AVAILABLE CARRIERS + TRUCKS:
${JSON.stringify(availCarriers,null,1)}

RULES: Driver needs ≥4h HOS at scheduled time. Minimize deadhead gallons. Favor carriers with lower detention hours and tighter over/short records. If terminal is HIGH congestion, recommend earlier or later slot to avoid peak.

Respond with ONLY valid JSON (no markdown):
{"carrierId":"c1","truckId":"SFT-04","recommendedTime":"10:30","reasoning":"2-3 specific sentences citing actual data","warnings":["any warnings"],"estimatedCost":1240,"fitScore":94}`;

      const res = await fetch("https://api.anthropic.com/v1/messages",{
        method:"POST",
        headers:{"Content-Type":"application/json","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01"},
        body:JSON.stringify({model:"claude-sonnet-4-6",max_tokens:500,messages:[{role:"user",content:prompt}]}),
      });
      const data = await res.json();
      const raw = data.content?.[0]?.text||"{}";
      const parsed = JSON.parse(raw.replace(/```json|```/g,"").trim());
      setAiDispatchResult(parsed);
      if(parsed.carrierId)    setDispatchCarrierId(parsed.carrierId);
      if(parsed.truckId)      setDispatchTruckId(parsed.truckId);
      if(parsed.recommendedTime) setScheduleTime(parsed.recommendedTime);
      addToast(" AI dispatch recommendation ready");
    } catch(e) {
      setAiDispatchResult({error:"Connect your Anthropic API key to enable AI dispatch. Add key to the API call in the source."});
    }
    setAiDispatchLoading(false);
  };

  const getWeekDates = (offset) => {
    const base = new Date(2025, 3, 16); // Apr 16 2025 = our "today" base.setDate(base.getDate() + offset * 7);
    // Go to Monday
    const day = base.getDay();
    const diff = day===0 ? -6 : 1-day;
    base.setDate(base.getDate() + diff);
    const days = [];
    for(let i=0;i<7;i++){
      const d = new Date(base); d.setDate(d.getDate()+i);
      days.push({ label:["MON","TUE","WED","THU","FRI","SAT","SUN"][i], num:d.getDate(), isToday:(i===2&&offset===0) });
    }
    return days;
  };

  const doDispatch = () => {
    if (!dispatchTarget || !dispatchCarrierId || !dispatchTruckId) return;
    const carrier = CARRIER_FLEET.find(c=>c.id===dispatchCarrierId);
    const tractor = carrier?.tractors.find(t=>t.id===dispatchTruckId);
    const store = STORES.find(s=>s.id===dispatchTarget.storeId);
    const terminal = TERMINALS.find(t=>t.id===store?.terminal);
    if (!carrier||!tractor||!store) return;
    const newId = "LD-" + (4400+liveLoads.length+1);
    const isToday = scheduleDate==="2025-04-18";
    const newLoad = {
      id:newId, carrier:carrier.short, truck:tractor.unit, driver:tractor.driver,
      origin:terminal?.name||"Terminal", dest:store.name,
      grade:dispatchTarget.grade, gals:dispatchTarget.vol,
      status:isToday?"LOADING":"SCHEDULED",
      pct:0, bol:null, tempF:null, apiGravity:null, bsmtTicket:null,
      eta:scheduleTime, departed:isToday?scheduleTime:null, detained:0, isNew:true,
      scheduledDate:scheduleDate, scheduledTime:scheduleTime,
      aiRecommended:!!aiDispatchResult&&!aiDispatchResult.error,
    };
    setLiveLoads(prev=>[...prev, newLoad]);
    setShowDispatchModal(false);
    setDispatchTarget(null); setDispatchCarrierId(null); setDispatchTruckId(null);
    setAiDispatchResult(null); setScheduleDate("2025-04-18"); setScheduleTime("10:00");
    addToast(` ${newId} ${isToday?"dispatched":"scheduled for "+scheduleDate} — ${tractor.driver} → ${store.name}`);
  };

  //  Signal Badge 
  const SignalBadge = ({ signal, color, size="sm" }) => {
    const big = size==="lg";
    return (
      <span style={{ display:"inline-flex", alignItems:"center", gap:4, padding:big?"6px 14px":"3px 9px",
        borderRadius:20, background:`${color}18`, border:`1.5px solid ${color}40`,
        color, fontWeight:800, fontFamily:"Arial,sans-serif", fontSize:big?13:10,
        letterSpacing:.3, whiteSpace:"nowrap" }}>
        {signal==="BUY NOW"&&" "}{signal==="WAIT"&&""}{signal==="SCHEDULE"&&" "}{signal==="ON PLAN"&&" "}
        {signal}
      </span>
    );
  };

  //  Forecast Band Chart 
  const ForecastBand = ({ pts, color, h=90, C, showDivider=true }) => {
    const W=560, H=h, bl=38, br=8, bt=8, bb=18;
    const IW=W-bl-br, IH=H-bt-bb;
    const allV = pts.flatMap(p=>[p.lo,p.hi]);
    const mn=Math.min(...allV)-0.002, mx=Math.max(...allV)+0.002, rng=mx-mn||.01;
    const px=i=>(i/(pts.length-1))*IW+bl;
    const py=v=>IH+bt-(v-mn)/rng*IH;
    const mid=pts.map((p,i)=>`${i===0?"M":"L"}${px(i).toFixed(1)},${py(p.val).toFixed(1)}`).join(" ");
    const hi=pts.map((p,i)=>`${i===0?"M":"L"}${px(i).toFixed(1)},${py(p.hi).toFixed(1)}`).join(" ");
    const lo=pts.slice().reverse().map((p,i)=>`L${px(pts.length-1-i).toFixed(1)},${py(p.lo).toFixed(1)}`).join(" ");
    const band=hi+" "+lo+" Z";
    const FONT="Arial,sans-serif";
    const yVals=[mn+(mx-mn)*0, mn+(mx-mn)*0.5, mn+(mx-mn)*1];
    return (
      <svg width="100%" viewBox={`0 0 ${W} ${H}`} preserveAspectRatio="none" style={{display:"block"}}>
        <defs>
          <linearGradient id={`fb${color.replace(/[^a-z0-9]/gi,"")}`} x1="0" y1="0" x2="1" y2="0">
            <stop offset="0%" stopColor={color} stopOpacity="0.06"/>
            <stop offset="100%" stopColor={color} stopOpacity="0.18"/>
          </linearGradient>
        </defs>
        {yVals.map((v,i)=>{
          const y=py(v);
          return <g key={i}>
            <line x1={bl} y1={y} x2={W-br} y2={y} stroke={C.cardBord} strokeWidth="0.45" strokeDasharray={i===1?"4,6":"none"}/>
            <text x={bl-4} y={y+3.5} textAnchor="end" fontSize="6.5" fill={C.textMut} fontFamily={FONT} fontWeight="700">${v.toFixed(4)}</text>
          </g>;
        })}
        {showDivider && <line x1={px(0)} y1={bt} x2={px(0)} y2={IH+bt} stroke={C.gold} strokeWidth="1" strokeDasharray="3,3" opacity="0.5"/>}
        <path d={band} fill={`url(#fb${color.replace(/[^a-z0-9]/gi,"")})`} stroke="none"/>
        <path d={hi} fill="none" stroke={color} strokeWidth="0.6" strokeDasharray="3,4" strokeOpacity="0.4"/>
        <path d={pts.slice().reverse().map((p,i)=>`${i===0?"M":"L"}${px(pts.length-1-i).toFixed(1)},${py(p.lo).toFixed(1)}`).join(" ")} fill="none" stroke={color} strokeWidth="0.6" strokeDasharray="3,4" strokeOpacity="0.4"/>
        <path d={mid} fill="none" stroke={color} strokeWidth="1.8" strokeLinecap="round" strokeLinejoin="round"/>
        {pts.map((p,i)=>{
          if(i!==0&&i!==6&&i!==13) return null;
          return <g key={i}>
            <circle cx={px(i)} cy={py(p.val)} r="3" fill={color}/>
            <text x={px(i)} y={H-3} textAnchor={i===0?"start":i===pts.length-1?"end":"middle"} fontSize="6.5" fill={C.textMut} fontFamily={FONT} fontWeight="700">
              {i===0?"Today":`Day ${p.day}`}
            </text>
            <text x={px(i)} y={py(p.val)-6} textAnchor="middle" fontSize="7" fill={color} fontFamily={FONT} fontWeight="700">${p.val.toFixed(4)}</text>
          </g>;
        })}
      </svg>
    );
  };

  //  Derived KPIs 
  const totalDailyVol = useMemo(() => STORES.reduce((a, s) => a + s.totalDailyVol, 0), []);
  const avgBlendedMargin = useMemo(() => STORES.reduce((a, s) => a + s.blendedMargin, 0) / STORES.length, []);
  const lowInvStores = useMemo(() => STORES.filter(s => GRADES.some(g => s.daysSupply[g] < 1.5)).length, []);
  const activeOrders = ORDERS.filter(o => o.statusIdx < 5).length;
  const pendingOrders = ORDERS.filter(o => o.statusIdx < 2).length;
  const todayGrossMargin = (avgBlendedMargin * totalDailyVol).toFixed(0);

  //  Tab: Command Center 
  const renderDashboard = () => {
    const FONT = "Arial,sans-serif";

    const critical = DEPLETION.filter(d=>d.minCritical<=1).sort((a,b)=>a.minCritical-b.minCritical);
    const urgent   = DEPLETION.filter(d=>d.minCritical>1&&d.minReorder<=1.5).sort((a,b)=>a.minReorder-b.minReorder);
    const reorder  = DEPLETION.filter(d=>d.minReorder>1.5&&d.minReorder<=3).sort((a,b)=>a.minReorder-b.minReorder);
    const onPlan   = DEPLETION.filter(d=>d.minReorder>3);
    const allNeedy = [...critical,...urgent,...reorder];
    const gallonsNeeded24h = [...critical,...urgent].reduce((acc,d)=>{
      const s=STORES.find(x=>x.id===d.storeId);
      return acc+(s?GRADES.reduce((a,g)=>a+(s.tanks[g]||0)*0.75,0):0);
    },0);
    const availTrucks = CARRIER_FLEET.reduce((a,c)=>a+c.available,0);
    const inTransit   = liveLoads.filter(l=>["EN ROUTE","LOADING","DELIVERING"].includes(l.status)).length;

    // Build alerts
    const alerts = [];
    critical.forEach(d=>{
      const s=STORES.find(x=>x.id===d.storeId), t=TERMINALS.find(t=>t.id===s?.terminal);
      const avail=CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(s?.terminal||""));
      const dispatched=liveLoads.some(l=>l.dest===s?.name&&["SCHEDULED","LOADING","EN ROUTE"].includes(l.status));
      const urgGrade=GRADES.find(g=>d.forecast[g]?.daysToCritical<=1)||"Regular";
      const vol=Math.round((s?.tanks?.[urgGrade]||8000)*0.78/500)*500;
      alerts.push({id:`crit-${d.storeId}`,level:"CRITICAL",title:`${s?.name} — ${urgGrade} critical in ${d.minCritical.toFixed(1)}d`,
        detail:`${s?.state} · ${t?.short} · ${vol.toLocaleString()} gal · ${avail?avail.short+' avail':'No carrier'}`,
        action:dispatched?"dispatched":"dispatch",actionLabel:dispatched?"Dispatched":"Dispatch Now",
        storeId:d.storeId,terminal:s?.terminal,grade:urgGrade,vol,carrierId:avail?.id||null,color:"#EF4444"});
    });
    urgent.forEach(d=>{
      const s=STORES.find(x=>x.id===d.storeId),t=TERMINALS.find(t=>t.id===s?.terminal);
      const avail=CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(s?.terminal||""));
      const dispatched=liveLoads.some(l=>l.dest===s?.name&&["SCHEDULED","LOADING","EN ROUTE"].includes(l.status));
      const urgGrade=GRADES.find(g=>d.forecast[g]?.daysToReorder<=1.5)||"Regular";
      const vol=Math.round((s?.tanks?.[urgGrade]||8000)*0.78/500)*500;
      alerts.push({id:`urg-${d.storeId}`,level:"URGENT",title:`${s?.name} — reorder in ${d.minReorder.toFixed(1)}d`,
        detail:`${s?.state} · ${t?.short} · ${vol.toLocaleString()} gal`,
        action:dispatched?"dispatched":"dispatch",actionLabel:dispatched?"Dispatched":"Dispatch",
        storeId:d.storeId,terminal:s?.terminal,grade:urgGrade,vol,carrierId:avail?.id||null,color:"#F59E0B"});
    });
    TERMINALS.forEach(t=>{GRADES.forEach(g=>{const sig=SIGNALS[t.id]?.[g];if(sig?.urgency>=3)alerts.push({
      id:`sig-${t.id}-${g}`,level:"BUY SIGNAL",title:`${sig.signal}: ${g} at ${t.short}`,
      detail:sig.reason,subdetail:sig.savingsNote,action:"rack",actionLabel:"View Prices",color:"#059669"});});});
    if(COLONIAL.line1Capacity<97)alerts.push({id:"col-l1",level:"PIPELINE",
      title:`Colonial Line 1 at ${COLONIAL.line1Capacity}%`,
      detail:"Reduced throughput — spot sourcing may be limited",action:"rack",actionLabel:"Check Rack",color:"#0D9488"});
    alerts.push({id:"nom",level:"DEADLINE",title:`Colonial nomination in 5.5h`,
      detail:`${COLONIAL.nominationDeadline} — submit Apr 17+ lifts now or wait 10 days`,action:"rack",actionLabel:"Nominate",color:"#EA580C"});
    Object.entries(TERMINAL_STATUS).forEach(([tid,ts])=>{if(ts.rackWait>30){const t=TERMINALS.find(x=>x.id===tid);
      alerts.push({id:`rack-${tid}`,level:"CONGESTION",title:`${t?.short} rack wait ${ts.rackWait}min`,
        detail:`${ts.lanesOpen}/${ts.lanesTotal} lanes · adjust dispatch window`,action:"dispatch",actionLabel:"Dispatch",color:"#0891B2"});}});
    reorder.slice(0,3).forEach(d=>{const s=STORES.find(x=>x.id===d.storeId),t=TERMINALS.find(x=>x.id===s?.terminal);
      alerts.push({id:`reord-${d.storeId}`,level:"REORDER",title:`${s?.name} — schedule in ${d.minReorder.toFixed(1)}d`,
        detail:`${s?.state} · ${t?.short}`,action:"dispatch",actionLabel:"Schedule",color:"#F4D398"});});
    const levelOrder={CRITICAL:0,URGENT:1,"BUY SIGNAL":2,DEADLINE:3,PIPELINE:4,CONGESTION:5,REORDER:6};
    alerts.sort((a,b)=>(levelOrder[a.level]??9)-(levelOrder[b.level]??9));

    const levelBg=(level)=>({
      CRITICAL:darkMode?"rgba(239,68,68,.13)":"#FFF5F5",URGENT:darkMode?"rgba(245,158,11,.10)":"#F8FAFB",
      "BUY SIGNAL":darkMode?"rgba(5,150,105,.10)":"#F0FDF4",DEADLINE:darkMode?"rgba(234,88,12,.10)":"#FFF7ED",
      PIPELINE:darkMode?"rgba(13,148,136,.10)":"#F0FDFA",CONGESTION:darkMode?"rgba(8,145,178,.10)":"#ECFEFF",
      REORDER:darkMode?"rgba(200,164,74,.08)":"#FFFDF0"}[level]||"transparent");

    return (
      <div style={{display:"flex",flexDirection:"column",gap:12}}>

        {/* Attention bar — today's single call-to-action */}
        <div data-tour="attention-bar">
          <AttentionBar
            critical={critical} urgent={urgent} reorder={reorder} alerts={alerts}
            availTrucks={availTrucks}
            onDispatch={()=>{
              const top = critical[0] || urgent[0];
              if (!top) return;
              const store = STORES.find(s=>s.id===top.storeId);
              const urgGrade = GRADES.find(g=>top.forecast[g]?.daysToReorder<=3)||"Regular";
              const vol = Math.round((store?.tanks?.[urgGrade]||8000)*0.78/500)*500;
              const avail = CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(store?.terminal||""));
              setDispatchTarget({storeId:top.storeId,grade:urgGrade,vol,storeName:store?.name,terminal:store?.terminal});
              setDispatchCarrierId(avail?.id||null); setDispatchTruckId(null);
              setDispatchCrumb(`Critical alert · ${store?.name||"store"}`);
              setShowDispatchModal(true);
            }}
            onViewAlerts={()=>{
              const feed = document.querySelector("[data-tour='alert-feed']");
              if (feed) feed.scrollIntoView({behavior:"smooth",block:"center"});
            }}
            darkMode={darkMode}
          />
        </div>

        {/* KPI strip — 4 purposeful stats, each a shortcut to its related view */}
        {/* The attention bar above already tells you what to DO today, so these */}
        {/* just give quick context you can scan in 2 seconds. Clicking any card */}
        {/* filters the alert feed or jumps to the related tab.                   */}
        <div style={{display:"flex",gap:8}}>
          {[
            {
              label:"Critical Stores", val:critical.length, sub:"need fuel today",
              color:"#EF4444",
              onClick: ()=>setAlertLevelFilter(critical.length>0 ? "CRITICAL" : "ALL"),
              hint: "Filter alerts → critical",
            },
            {
              label:"Urgent Stores", val:urgent.length, sub:"reorder <1.5 days",
              color:"#F59E0B",
              onClick: ()=>setAlertLevelFilter(urgent.length>0 ? "URGENT" : "ALL"),
              hint: "Filter alerts → urgent",
            },
            {
              label:"Gal to Move Today", val:`${(gallonsNeeded24h/1000).toFixed(0)}K`, sub:"critical + urgent",
              color:"#EF4444",
              onClick: ()=>setActiveTab("dispatch"),
              hint: "Open Dispatch",
            },
            {
              label:"Trucks Available", val:availTrucks, sub:`${inTransit} in transit`,
              color: availTrucks>5?"#22C55E":"#F59E0B",
              onClick: ()=>setActiveTab("dispatch"),
              hint: "Open Dispatch",
            },
          ].map((k,i)=>(
            <div key={i} onClick={k.onClick} title={k.hint}
              style={{
                flex:1, cursor:"pointer", transition:"transform .12s, box-shadow .12s",
              }}
              onMouseEnter={e=>{e.currentTarget.style.transform="translateY(-1px)";e.currentTarget.style.boxShadow="0 4px 12px rgba(0,0,0,.08)";}}
              onMouseLeave={e=>{e.currentTarget.style.transform="none";e.currentTarget.style.boxShadow="none";}}>
              <KpiCard {...k} C={C} darkMode={darkMode}/>
            </div>
          ))}
        </div>

        {/* Main row */}
        <div style={{display:"flex",gap:14}}>

          {/* Alert feed */}
          <div data-tour="alert-feed" style={{flex:"0 0 500px",background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden",display:"flex",flexDirection:"column"}}>
            <div style={{padding:"12px 16px",borderBottom:`1px solid ${C.cardBord}`,display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0}}>
              <div>
                <div style={{fontSize:13,fontWeight:700,color:C.textPri,fontFamily:FONT}}>Active Alerts</div>
                <div style={{fontSize:10.5,color:C.textSec,marginTop:1}}>{alerts.length} open · {alerts.filter(a=>a.level==="CRITICAL").length} critical · sorted by priority</div>
              </div>
              <button onClick={()=>setShowAdvisor(true)} style={{padding:"5px 12px",borderRadius:6,border:`1px solid ${C.gold}`,background:darkMode?"rgba(200,164,74,.12)":"#FFF9E6",color:C.gold,fontSize:11,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                AI Briefing
              </button>
            </div>
            <div style={{display:"flex",gap:4,padding:"8px 12px",borderBottom:`1px solid ${C.cardBord}`,flexWrap:"wrap",flexShrink:0}}>
              {["ALL",...[...new Set(alerts.map(a=>a.level))]].map(lv=>{
                const col={CRITICAL:"#EF4444",URGENT:"#F59E0B","BUY SIGNAL":"#059669",DEADLINE:"#EA580C",PIPELINE:"#475569",CONGESTION:"#0891B2",REORDER:"#F4D398"}[lv]||C.textSec;
                const cnt=lv==="ALL"?alerts.length:alerts.filter(a=>a.level===lv).length;
                return <button key={lv} onClick={()=>setAlertLevelFilter(lv)}
                  style={{padding:"2px 9px",borderRadius:10,border:`1.5px solid ${alertLevelFilter===lv?col:C.cardBord}`,background:alertLevelFilter===lv?`${col}22`:"transparent",color:alertLevelFilter===lv?col:C.textSec,fontSize:9.5,fontWeight:alertLevelFilter===lv?700:400,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap"}}>
                  {lv} {cnt>0&&`(${cnt})`}
                </button>;
              })}
            </div>
            <div style={{overflowY:"auto",flex:1}}>
              {(alertLevelFilter==="ALL"?alerts:alerts.filter(a=>a.level===alertLevelFilter)).map(alert=>{
                const isDispatched=alert.action==="dispatched";
                return (
                  <div key={alert.id} style={{padding:"10px 14px",borderBottom:`1px solid ${C.cardBord}`,background:levelBg(alert.level),display:"flex",gap:10,alignItems:"flex-start"}}>
                    <div style={{width:3,borderRadius:2,background:alert.color,flexShrink:0,alignSelf:"stretch",minHeight:36}}/>
                    <div style={{flex:1,minWidth:0}}>
                      <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:3}}>
                        <span style={{fontSize:8.5,fontWeight:800,padding:"2px 6px",borderRadius:4,background:`${alert.color}22`,color:alert.color,letterSpacing:.4,textTransform:"uppercase",flexShrink:0,border:`1px solid ${alert.color}30`}}>{alert.level}</span>
                        <span style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,lineHeight:1.3}}>{alert.title}</span>
                      </div>
                      <div style={{fontSize:10,color:C.textSec,paddingLeft:1}}>{alert.detail}</div>
                      {alert.subdetail&&<div style={{fontSize:9.5,color:alert.color,fontWeight:600,paddingLeft:1,marginTop:1}}>{alert.subdetail}</div>}
                    </div>
                    <div style={{flexShrink:0}}>
                      {isDispatched
                        ? <span style={{fontSize:9.5,fontWeight:700,padding:"3px 9px",borderRadius:5,background:darkMode?"rgba(34,197,94,.15)":"#F0FDF4",color:"#22C55E",border:"1px solid rgba(34,197,94,.3)"}}>Dispatched</span>
                        : alert.action==="dispatch"
                        ? <button onClick={()=>{const sn=STORES.find(s=>s.id===alert.storeId)?.name;setDispatchTarget({storeId:alert.storeId,grade:alert.grade,vol:alert.vol,storeName:sn,terminal:alert.terminal});setDispatchCarrierId(alert.carrierId||null);setDispatchTruckId(null);setDispatchCrumb(`${alert.level} alert · ${sn||"store"} · ${alert.grade}`);setShowDispatchModal(true);}}
                            style={{padding:"4px 10px",borderRadius:5,border:`1.5px solid ${alert.color}`,background:`${alert.color}18`,color:alert.color,fontSize:10,fontWeight:700,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap"}}>{alert.actionLabel}</button>
                        : <button onClick={()=>{setDispatchCrumb(`${alert.level} alert · ${alert.title}`);setActiveTab(alert.action==="rack"?"rack":"dispatch");}}
                            style={{padding:"4px 10px",borderRadius:5,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:10,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap"}}>{alert.actionLabel}</button>
                      }
                    </div>
                  </div>
                );
              })}
            </div>
          </div>

          {/* Right: Today's schedule + 7-day depletion heatmap */}
          <div data-tour="command-schedule" style={{flex:1,display:"flex",flexDirection:"column",gap:12,minWidth:0}}>

            {/* Today's Schedule — what's already in motion */}
            <TodaysSchedule
              loads={liveLoads}
              onJumpToDispatch={()=>setActiveTab("dispatch")}
              onSelectLoad={(ld)=>{ setSelectedLoad(ld); setActiveTab("dispatch"); }}
              darkMode={darkMode} C={C} FONT={FONT}
            />

            {/* Depletion heatmap — compact */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:14}}>
              <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:10}}>
                <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>7-Day Depletion Heatmap</div>
                <button onClick={()=>setActiveTab("inventory")} style={{fontSize:10,color:C.gold,background:"none",border:"none",cursor:"pointer",fontWeight:700,fontFamily:FONT}}>Full Inventory →</button>
              </div>
              <div style={{display:"flex",gap:0}}>
                <div style={{flexShrink:0,borderRight:`1px solid ${C.cardBord}`}}>
                  <div style={{height:22,display:"flex",alignItems:"center",padding:"0 10px",fontSize:8,fontWeight:700,color:C.textMut,borderBottom:`1px solid ${C.cardBord}`,minWidth:120}}>STORE</div>
                  {allNeedy.slice(0,9).map(d=>(
                    <div key={d.storeId} style={{height:22,display:"flex",alignItems:"center",padding:"0 10px",fontSize:9.5,color:d.minCritical<=1?"#EF4444":C.textPri,fontWeight:d.minCritical<=1?700:400,borderBottom:`1px solid ${C.cardBord}`,minWidth:120,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>
                      {STORES.find(s=>s.id===d.storeId)?.name}
                    </div>
                  ))}
                </div>
                <div style={{flex:1}}>
                  <div style={{display:"flex"}}>
                    {[0,1,2,3,4,5,6].map(day=>(
                      <div key={day} style={{flex:1}}>
                        <div style={{height:22,display:"flex",alignItems:"center",justifyContent:"center",fontSize:8.5,fontWeight:700,color:day===0?C.gold:C.textMut,borderBottom:`1px solid ${C.cardBord}`,borderLeft:`1px solid ${C.cardBord}`,background:day===0?(darkMode?"rgba(200,164,74,.06)":"#FDFAF0"):"transparent"}}>
                          {day===0?"Now":"+" + day + "d"}
                        </div>
                        {allNeedy.slice(0,9).map(d=>{
                          const isCrit=d.minCritical<=day,isReord=d.minReorder<=day&&!isCrit;
                          const cellBg = isCrit?(darkMode?"rgba(239,68,68,.25)":"#FEE2E2"):isReord?(darkMode?"rgba(245,158,11,.18)":"#FEF9C3"):(darkMode?"rgba(34,197,94,.05)":"#F0FDF4");
                          const dotBg  = isCrit?"#EF4444":isReord?"#F59E0B":"#22C55E";
                          const dotOp  = isCrit?1:isReord?0.7:0.2;
                          return <div key={d.storeId} style={{height:22,borderBottom:"1px solid "+C.cardBord,borderLeft:"1px solid "+C.cardBord,background:cellBg,display:"flex",alignItems:"center",justifyContent:"center"}}>
                            <div style={{width:8,height:8,borderRadius:2,background:dotBg,opacity:dotOp}}/>
                          </div>;
                        })}
                      </div>
                    ))}
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    );
  };

  //  Tab: Rack Prices 
  //  Tab: Rack Prices 
  const renderRackPrices = () => {
    const hist = RACK_HISTORY[selectedTerminal]?.[selectedGrade] || [];
    const term = TERMINALS.find(t => t.id === selectedTerminal);
    const rack = RACK_PRICES[selectedTerminal]?.[selectedGrade] || 0;
    const diff = CONTRACT_DIFF[selectedTerminal]?.[selectedGrade] || 0;
    const freight = FREIGHT[selectedTerminal] || 0;
    const SPOT_ADDER = 0.0285; // open-market adder above rack

    // Full landed cost for the active state (NC default for display)
    const stateTax = STATE_TAX.NC;
    const contractLanded = rack + diff + freight + stateTax + FED_TAX;
    const spotLanded     = rack + SPOT_ADDER + freight + stateTax + FED_TAX;
    const spotIsCheaper  = spotLanded < contractLanded;
    const deltaCPG       = Math.abs(contractLanded - spotLanded);

    // Cost stack segments for stacked bar
    const stackSegs = [
      { label:"Rack",         val:rack,      color:"#BBD5EF" },
      { label:"State Tax",    val:stateTax,  color:"#848270" },
      { label:"Fed Excise",   val:FED_TAX,   color:"#F4D398" },
      { label:"Freight",      val:freight,   color:"#3E6387" },
    ];
    const contractExtra = { label:"Contract Diff", val:diff,       color:"#EFEFEF" };
    const spotExtra      = { label:"Spot Adder",    val:SPOT_ADDER, color:"#BBD5EF" };
    const contractSegs = [...stackSegs, contractExtra];
    const spotSegs     = [...stackSegs, spotExtra];
    const maxBar = Math.max(contractLanded, spotLanded);

    // Savings calc at various volumes
    const savingsAtVol = liftVol * deltaCPG;
    const winner = spotIsCheaper ? "spot" : "contract";

    // All-terminal scorecard
    const termCards = TERMINALS.map(t => {
      const r  = RACK_PRICES[t.id][selectedGrade];
      const d  = CONTRACT_DIFF[t.id][selectedGrade];
      const fr = FREIGHT[t.id];
      const cL = r + d  + fr + stateTax + FED_TAX;
      const sL = r + SPOT_ADDER + fr + stateTax + FED_TAX;
      const cheaper = sL < cL ? "spot" : "contract";
      const delta   = Math.abs(cL - sL);
      return { term:t, contractLanded:cL, spotLanded:sL, cheaper, delta, rack:r };
    }).sort((a,b) => Math.min(a.contractLanded,a.spotLanded) - Math.min(b.contractLanded,b.spotLanded));

    // Days spot has been cheaper (simulate from history)
    // Stable per-terminal spot win days (seeded by terminal id, not random on each render)
    const spotWinSeed = {"selma":14,"charlotte":17,"richmond":12,"atlanta":19,"jacksonville":15,"tampa":16};
    const spotWinDays = spotWinSeed[selectedTerminal] ?? 15;

    const FONT = "Arial,sans-serif";

    // Stacked bar render function
    const renderStackBar = (segs, total, landed, isWinner, label) => {
      const W = 260, H = 160;
      let x = 0;
      const pxPerDollar = W / maxBar;
      return (
        <div style={{ flex:1 }}>
          <div style={{ fontSize:10, color:C.textMut, textTransform:"uppercase", letterSpacing:.6, fontFamily:FONT, marginBottom:8 }}>{label}</div>
          {/* Horizontal stacked bar */}
          <div style={{ height:32, background:C.cardBord, borderRadius:6, overflow:"hidden", marginBottom:10, position:"relative" }}>
            {segs.map((s,i) => {
              const leftPct = (segs.slice(0,i).reduce((a,v)=>a+v.val,0)/maxBar)*100;
              const widthPct = (s.val / maxBar) * 100;
              // Estimate if label fits: ~6px per char, need padding; bar width in px ≈ widthPct/100 * containerWidth
              // Use 260px as approximate container width; label is "$0.0000" = 7 chars ≈ 52px + 8px padding = 60px min
              const estPx = (widthPct / 100) * 260;
              const labelFits = estPx >= 38;
              // Pick text color based on background luminance
              const darkBg = ["#BBD5EF","#3E6387","#848270"].includes(s.color);
              const textCol = darkBg ? "#fff" : s.color==="#EFEFEF"||s.color==="#F4D398"||s.color==="#BBD5EF" ? "#BBD5EF" : "#fff";
              return (
                <div key={i} title={`${s.label}: $${s.val.toFixed(4)}`} style={{
                  position:"absolute", left:`${leftPct}%`,
                  width:`${widthPct}%`, height:"100%", background:s.color,
                  transition:"width .3s", display:"flex", alignItems:"center", justifyContent:"center",
                  overflow:"hidden" }}>
                  {labelFits && (
                    <span style={{ fontSize:9, fontWeight:700, color:textCol, fontFamily:"Arial,sans-serif", whiteSpace:"nowrap", letterSpacing:-.2 }}>
                      ${s.val.toFixed(4)}
                    </span>
                  )}
                </div>
              );
            })}
          </div>
          {/* Landed cost big number */}
          <div style={{ display:"flex", alignItems:"baseline", gap:6, marginBottom:10 }}>
            <span style={{ fontSize:28, fontWeight:900, color:isWinner?C.green:C.textPri, fontFamily:FONT, lineHeight:1 }}>${landed.toFixed(4)}</span>
            <span style={{ fontSize:11, color:C.textSec, fontFamily:FONT }}>/gal landed</span>
            {isWinner && <span style={{ fontSize:11, fontWeight:700, color:C.green, background:darkMode?"rgba(34,197,94,.15)":"#F0FDF4", border:`1px solid ${C.green}40`, borderRadius:20, padding:"2px 10px", fontFamily:FONT }}> CHEAPER</span>}
          </div>
          {/* Component rows */}
          {segs.map((s,i) => (
            <div key={i} style={{ display:"flex", alignItems:"center", justifyContent:"space-between", padding:"4px 0", borderBottom:`1px solid ${C.cardBord}` }}>
              <div style={{ display:"flex", alignItems:"center", gap:6 }}>
                <div style={{ width:8, height:8, borderRadius:2, background:s.color, flexShrink:0 }}/>
                <span style={{ fontSize:10.5, color:C.textSec, fontFamily:FONT }}>{s.label}</span>
              </div>
              <span style={{ fontSize:10.5, fontWeight:600, color:C.textPri, fontFamily:FONT }}>${s.val.toFixed(4)}</span>
            </div>
          ))}
          <div style={{ display:"flex", justifyContent:"space-between", padding:"6px 0", marginTop:2 }}>
            <span style={{ fontSize:11, fontWeight:700, color:C.textSec, fontFamily:FONT }}>Total Landed</span>
            <span style={{ fontSize:12, fontWeight:800, color:isWinner?C.green:C.textPri, fontFamily:FONT }}>${landed.toFixed(4)}</span>
          </div>
        </div>
      );
    };

    return (
      <div style={{ display:"flex", flexDirection:"column", gap:14 }}>

        {/*  GRADE + TERMINAL SELECTORS  */}
        <div style={{ display:"flex", gap:8, alignItems:"center", flexWrap:"wrap" }}>
          {GRADES.map(g => {
            const gc = {Regular:"#3B82F6",Premium:"#8B5CF6",Diesel:"#F59E0B"}[g];
            const active = selectedGrade===g;
            return (
              <button key={g} onClick={()=>setSelectedGrade(g)} style={{
                padding:"7px 18px", borderRadius:7, border:`1.5px solid ${active?gc:C.cardBord}`,
                background:active?(darkMode?`${gc}22`:`${gc}18`):"transparent",
                color:active?gc:C.textSec, fontSize:12, fontWeight:active?800:400,
                cursor:"pointer", fontFamily:FONT, transition:"all .15s",
              }}>{g}</button>
            );
          })}
          <div style={{ width:1, height:22, background:C.cardBord, margin:"0 4px" }}/>
          {TERMINALS.map(t => (
            <button key={t.id} onClick={()=>setSelectedTerminal(t.id)} style={{
              padding:"7px 14px", borderRadius:7, border:`1.5px solid ${selectedTerminal===t.id?C.gold:C.cardBord}`,
              background:selectedTerminal===t.id?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent",
              color:selectedTerminal===t.id?C.gold:C.textSec, fontSize:12,
              fontWeight:selectedTerminal===t.id?700:400, cursor:"pointer", fontFamily:FONT,
            }}><ZoneBadge terminalId={t.id}/> {t.short}</button>
          ))}
        </div>

        {/*  DECISION BANNER  */}
        <div style={{
          borderRadius:8,
          background:spotIsCheaper
            ? (darkMode?"rgba(34,197,94,.1)":"#F0FDF4")
            : (darkMode?"rgba(200,164,74,.1)":"#F8FAFB"),
          border:`1.5px solid ${spotIsCheaper?C.green:C.gold}`,
          display:"flex", alignItems:"center", justifyContent:"space-between", gap:16, padding:"10px 16px",
        }}>
          <div style={{ display:"flex", alignItems:"center", gap:12 }}>
            <div>
              <div style={{ fontSize:10, color:spotIsCheaper?C.green:C.gold, fontWeight:700, textTransform:"uppercase", letterSpacing:.8, fontFamily:FONT, marginBottom:2 }}>
                Today's Recommendation — {term?.name} · {selectedGrade}
              </div>
              <div style={{ fontSize:17, fontWeight:900, color:C.textPri, fontFamily:FONT, lineHeight:1.1 }}>
                {spotIsCheaper ? "Go Spot Market" : "Stay on Contract"}
              </div>
              <div style={{ fontSize:11, color:C.textSec, marginTop:3, fontFamily:FONT }}>
                {spotIsCheaper && !SPOT_CONSTRAINED
                  ? `Spot is $${deltaCPG.toFixed(4)}/gal cheaper — Colonial at ${COLONIAL.line1Capacity}% cap, spot barrels available` : spotIsCheaper && SPOT_CONSTRAINED
                  ? `Spot price is lower but Colonial is constrained (${COLONIAL.line1Capacity}%) — spot sourcing may be unreliable` : `Your contract beats spot by $${deltaCPG.toFixed(4)}/gal — protect your committed volume`}
              </div>
              {SPOT_CONSTRAINED && spotIsCheaper && (
                <div style={{ marginTop:4, display:"flex", alignItems:"center", gap:6, padding:"3px 9px", borderRadius:6, background:"rgba(251,191,36,.12)", border:"1px solid rgba(251,191,36,.3)", width:"fit-content" }}>
                  <span style={{ fontSize:10.5, color:C.amber, fontWeight:700, fontFamily:FONT }}>Colonial {COLONIAL.status} — verify spot allocation before committing</span>
                </div>
              )}
            </div>
          </div>
          <div style={{ display:"flex", gap:16, flexShrink:0 }}>
            {[
              { label:"Δ CPG",         val:`$${deltaCPG.toFixed(4)}`, color:spotIsCheaper?C.green:C.gold },
              { label:"30-Day Spot Wins",val:`${spotWinDays} days`,   color:C.textSec },
              { label:"Pipeline",       val:term?.pipeline||"",        color:C.textSec },
            ].map((stat,i) => (
              <div key={i} style={{ textAlign:"center" }}>
                <div style={{ fontSize:18, fontWeight:800, color:stat.color, fontFamily:FONT }}>{stat.val}</div>
                <div style={{ fontSize:9.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.5, fontFamily:FONT, marginTop:2 }}>{stat.label}</div>
              </div>
            ))}
          </div>
        </div>

        {/*  MAIN ROW: side-by-side cost stacks + savings calc + history  */}
        <div style={{ display:"flex", gap:14 }}>

          {/* Cost Bridge — shared components once, fork only where paths diverge */}
          <div style={{ flex:2, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:18 }}>
            <div style={{ fontSize:12, fontWeight:700, color:C.textPri, fontFamily:FONT, marginBottom:16 }}>
              Cost Breakdown — {term?.name} · {selectedGrade}
            </div>

            {/* Shared base components + donut side by side */}
            <div style={{display:"flex", gap:20, alignItems:"flex-start"}}>

              {/* Component rows */}
              <div style={{flex:1, minWidth:0}}>
            {[
              { label:"Rack Price",  val:rack,     note:"OPIS posted rack",    color:"#F4D398" },
              { label:"State Tax",   val:stateTax, note:"SE avg blended",      color:"#64748B" },
              { label:"Fed Excise",  val:FED_TAX,  note:"fixed",               color:"#94A3B8" },
              { label:"Freight",     val:freight,  note:`${term?.short} zone`, color:"#0D9488" },
              { label:spotIsCheaper?"Spot Adder":"Contract Diff", val:spotIsCheaper?SPOT_ADDER:diff, note:"path-specific", color: spotIsCheaper?"#EA580C":"#3B82F6" },
            ].map((row, i) => {
              const pct = (row.val / contractLanded * 100).toFixed(1);
              return (
              <div key={i} style={{
                display:"flex", justifyContent:"space-between", alignItems:"center",
                padding:"7px 10px",
                background: i===0 ? (darkMode?"rgba(255,255,255,.03)":"#F4F6F9") : "transparent",
                borderBottom: `1px solid ${C.cardBord}`,
                borderRadius: i===0 ? "6px 6px 0 0" : 0,
              }}>
                <div style={{display:"flex", alignItems:"center", gap:8, flex:1, minWidth:0}}>
                  <div style={{width:8, height:8, borderRadius:2, background:row.color, flexShrink:0}}/>
                  <span style={{ fontSize:11, color: i===0 ? C.textPri : C.textSec, fontWeight: i===0 ? 700 : 400, fontFamily:FONT, whiteSpace:"nowrap" }}>{row.label}</span>
                  <span style={{ fontSize:9.5, color:C.textMut, fontFamily:FONT, whiteSpace:"nowrap" }}>{row.note}</span>
                </div>
                <div style={{display:"flex", alignItems:"center", gap:10, flexShrink:0}}>
                  <span style={{fontSize:9.5, fontWeight:600, color:row.color, fontFamily:"Arial,sans-serif"}}>{pct}%</span>
                  <span style={{ fontSize:11, fontWeight: i===0 ? 700 : 500, color: i===0 ? C.textPri : C.textSec, fontFamily:"Arial,sans-serif", minWidth:60, textAlign:"right" }}>
                    ${row.val.toFixed(4)}
                  </span>
                </div>
              </div>
              );
            })}
              </div>

              {/* Donut chart */}
              {(() => {
                const segs = [
                  { label:"Rack",      val:rack,                                    color:"#F4D398" },
                  { label:"State Tax", val:stateTax,                                color:"#64748B" },
                  { label:"Fed Tax",   val:FED_TAX,                                 color:"#94A3B8" },
                  { label:"Freight",   val:freight,                                 color:"#0D9488" },
                  { label:spotIsCheaper?"Spot":"Contract Diff", val:spotIsCheaper?SPOT_ADDER:diff, color:spotIsCheaper?"#EA580C":"#3B82F6" },
                ];
                const total = segs.reduce((a,s)=>a+s.val,0);
                const cx=80, cy=80, R=72, r=44;
                let cumAngle = -Math.PI/2;
                const slices = segs.map(s => {
                  const angle = (s.val/total) * 2 * Math.PI;
                  const x1=cx+R*Math.cos(cumAngle), y1=cy+R*Math.sin(cumAngle);
                  cumAngle += angle;
                  const x2=cx+R*Math.cos(cumAngle), y2=cy+R*Math.sin(cumAngle);
                  const ix1=cx+r*Math.cos(cumAngle-angle), iy1=cy+r*Math.sin(cumAngle-angle);
                  const ix2=cx+r*Math.cos(cumAngle), iy2=cy+r*Math.sin(cumAngle);
                  const large = angle > Math.PI ? 1 : 0;
                  const d = `M${x1},${y1} A${R},${R},0,${large},1,${x2},${y2} L${ix2},${iy2} A${r},${r},0,${large},0,${ix1},${iy1} Z`;
                  return {...s, d, pct:(s.val/total*100).toFixed(1)};
                });
                return (
                  <div style={{flexShrink:0, display:"flex", flexDirection:"column", alignItems:"center", paddingTop:4}}>
                    <svg width={160} height={160} viewBox="0 0 160 160">
                      {slices.map((s,i)=>(
                        <path key={i} d={s.d} fill={s.color} opacity={.9}>
                          <title>{s.label}: {s.pct}%</title>
                        </path>
                      ))}
                      {/* Center label */}
                      <text x={cx} y={cy-6} textAnchor="middle" fontSize="11" fontWeight="800" fill={darkMode?"#E8EDF6":"#BBD5EF"} fontFamily="Arial,sans-serif">
                        ${contractLanded.toFixed(2)}
                      </text>
                      <text x={cx} y={cy+10} textAnchor="middle" fontSize="8.5" fill={darkMode?"#7B8FAF":"#64748B"} fontFamily="Arial,sans-serif">
                        landed/gal
                      </text>
                    </svg>
                  </div>
                );
              })()}

            </div>

            {/* Subtotal */}
            {(() => {
              const base = rack + stateTax + FED_TAX + freight;
              return (
                <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center", padding:"7px 10px", borderBottom:`2px solid ${C.cardBord}`, background: darkMode?"rgba(255,255,255,.02)":"#F8FAFC" }}>
                  <span style={{ fontSize:10.5, fontWeight:700, color:C.textSec, fontFamily:FONT, letterSpacing:.3 }}>BASE COST (shared)</span>
                  <span style={{ fontSize:11, fontWeight:800, color:C.textSec, fontFamily:"Arial,sans-serif" }}>${base.toFixed(4)}</span>
                </div>
              );
            })()}

            {/* Fork rows — only what differs */}
            <div style={{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:10, marginTop:12 }}>
              {[
                { label:"Contract Diff", val:diff,       total:contractLanded, isWinner:!spotIsCheaper, path:"Contract" },
                { label:"Spot Adder",    val:SPOT_ADDER, total:spotLanded,     isWinner:spotIsCheaper,  path:"Spot" },
              ].map((p, i) => (
                <div key={i} style={{
                  padding:"12px 14px", borderRadius:8,
                  border:`2px solid ${p.isWinner ? (spotIsCheaper ? C.green : C.gold) : C.cardBord}`,
                  background: p.isWinner ? (darkMode?"rgba(255,255,255,.03)":"#FAFCFF") : "transparent",
                }}>
                  <div style={{ fontSize:9.5, fontWeight:700, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:6, fontFamily:FONT }}>{p.path} Path</div>
                  <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center", marginBottom:10 }}>
                    <span style={{ fontSize:10.5, color:C.textSec, fontFamily:FONT }}>{p.label}</span>
                    <span style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif" }}>+${p.val.toFixed(4)}</span>
                  </div>
                  <div style={{ borderTop:`1px solid ${C.cardBord}`, paddingTop:8, display:"flex", justifyContent:"space-between", alignItems:"baseline" }}>
                    <span style={{ fontSize:10, color:C.textSec, fontFamily:FONT }}>Landed</span>
                    <span style={{ fontSize:20, fontWeight:900, fontFamily:"Arial,sans-serif", color: p.isWinner ? (spotIsCheaper ? C.green : C.gold) : C.textPri, lineHeight:1 }}>
                      ${p.total.toFixed(4)}
                    </span>
                  </div>
                  {p.isWinner && (
                    <div style={{ marginTop:6, fontSize:9.5, fontWeight:700, color: spotIsCheaper ? C.green : C.gold, fontFamily:FONT, textAlign:"right" }}>
                      saves ${deltaCPG.toFixed(4)}/gal
                    </div>
                  )}
                </div>
              ))}
            </div>
          </div>

          {/* Right column: savings calc + rack history */}
          <div style={{ width:270, flexShrink:0, display:"flex", flexDirection:"column", gap:14 }}>

            {/* Savings Calculator */}
            <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
              <div style={{ display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:12 }}>
                <div style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT }}>Savings Calculator</div>
                <button onClick={()=>setLiftVol(10000)}
                  style={{ padding:"4px 11px", borderRadius:6, border:`1px solid ${C.cardBord}`, background:liftVol===10000?(darkMode?"rgba(200,164,74,.15)":"#FFF9E6"):"transparent", color:liftVol===10000?C.gold:C.textSec, fontSize:10, fontWeight:liftVol===10000?700:500, cursor:"pointer", fontFamily:FONT, whiteSpace:"nowrap" }}>
                  1 Truckload (10K)
                </button>
              </div>
              <div style={{ fontSize:10, color:C.textSec, fontFamily:FONT, marginBottom:6 }}>Gallons to lift this order</div>
              <input type="range" min={10000} max={250000} step={5000} value={liftVol}
                onChange={e=>setLiftVol(+e.target.value)}
                style={{ width:"100%", accentColor:spotIsCheaper?C.green:C.gold, marginBottom:6 }}/>
              <div style={{ display:"flex", justifyContent:"space-between", marginBottom:12 }}>
                <span style={{ fontSize:10, color:C.textMut, fontFamily:FONT }}>10K gal</span>
                <span style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT }}>{(liftVol/1000).toFixed(0)}K gal</span>
                <span style={{ fontSize:10, color:C.textMut, fontFamily:FONT }}>250K gal</span>
              </div>
              <div style={{ textAlign:"center", padding:"14px 0", background:spotIsCheaper?(darkMode?"rgba(34,197,94,.1)":"#F0FDF4"):(darkMode?"rgba(200,164,74,.1)":"#F8FAFB"), borderRadius:8, border:`1px solid ${spotIsCheaper?C.green:C.gold}40` }}>
                <div style={{ fontSize:11, color:C.textSec, fontFamily:FONT, marginBottom:4 }}>
                  {spotIsCheaper?"Spot saves you":"Contract saves you"}
                </div>
                <div style={{ fontSize:28, fontWeight:900, color:spotIsCheaper?C.green:C.gold, fontFamily:FONT, lineHeight:1 }}>
                  ${savingsAtVol.toFixed(0).replace(/\B(?=(\d{3})+(?!\d))/g,",")}
                </div>
                <div style={{ fontSize:10, color:C.textSec, fontFamily:FONT, marginTop:4 }}>on this single lift</div>
              </div>
              <div style={{ display:"flex", flexDirection:"column", gap:4, marginTop:10 }}>
                {[50000,100000,200000].map(v=>(
                  <div key={v} style={{ display:"flex", justifyContent:"space-between", padding:"4px 8px", borderRadius:5, background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC" }}>
                    <span style={{ fontSize:10, color:C.textSec, fontFamily:FONT }}>{(v/1000).toFixed(0)}K gal</span>
                    <span style={{ fontSize:10.5, fontWeight:700, color:spotIsCheaper?C.green:C.gold, fontFamily:FONT }}>
                      ${(v*deltaCPG).toFixed(0).replace(/\B(?=(\d{3})+(?!\d))/g,",")}
                    </span>
                  </div>
                ))}
              </div>
            </div>

            {/* 30-day rack history */}
            <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
              <div style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT, marginBottom:4 }}>30-Day Rack History</div>
              <div style={{ fontSize:10, color:C.textSec, fontFamily:FONT, marginBottom:8 }}>{term?.name} · {selectedGrade}</div>
              <Spark data={hist} color="#3B82F6" h={52}/>
              <div style={{ display:"flex", justifyContent:"space-between", marginTop:8 }}>
                <div>
                  <div style={{ fontSize:9, color:C.textMut, fontFamily:FONT }}>30 days ago</div>
                  <div style={{ fontSize:12, fontWeight:700, color:C.textPri, fontFamily:FONT }}>${hist[0]?.toFixed(4)||"—"}</div>
                </div>
                <div style={{ textAlign:"right" }}>
                  <div style={{ fontSize:9, color:C.textMut, fontFamily:FONT }}>Today</div>
                  <div style={{ fontSize:12, fontWeight:700, color:C.textPri, fontFamily:FONT }}>${rack.toFixed(4)}</div>
                </div>
              </div>
              <div style={{ marginTop:8, textAlign:"center", fontSize:11, fontWeight:700, fontFamily:FONT, color:rack>(hist[0]||rack)?C.red:C.green }}>
                {rack>(hist[0]||rack)?" Up":" Down"} ${Math.abs(rack-(hist[0]||rack)).toFixed(4)} in 30 days
              </div>
              <div style={{ marginTop:6, fontSize:8.5, color:C.textMut, textAlign:"center", fontFamily:FONT, fontStyle:"italic" }}>
                Source: EIA weekly retail data (PADD 1C), rack-derived. Daily points interpolated between weekly releases.
              </div>
            </div>
          </div>
        </div>

        {/*  ALL-TERMINAL SCORECARD  */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:18 }}>
          <div style={{ fontSize:12, fontWeight:700, color:C.textPri, fontFamily:FONT, marginBottom:4 }}>All-Terminal Scorecard — {selectedGrade} · Best Landed Cost Today</div>
          <div style={{ fontSize:10.5, color:C.textSec, fontFamily:FONT, marginBottom:14 }}>Ranked by cheapest available path. Click any terminal to drill in.</div>
          <div style={{ display:"flex", gap:10 }}>
            {termCards.map((tc, i) => {
              const isActive   = tc.term.id === selectedTerminal;
              const cheapest   = Math.min(tc.contractLanded, tc.spotLanded);
              const cheapLabel = tc.cheaper === "spot" ? "Go Spot" : "Use Contract";
              const cheapColor = tc.cheaper === "spot" ? C.green : C.gold;
              const best = termCards[0];
              const vsFirst = cheapest - Math.min(best.contractLanded, best.spotLanded);
              const GRADE_COL = {Regular:"#3B82F6",Premium:"#8B5CF6",Diesel:"#F59E0B"}[selectedGrade]||C.gold;
              return (
                <div key={tc.term.id} onClick={()=>setSelectedTerminal(tc.term.id)}
                  style={{
                    flex:1, borderRadius:10, padding:"14px 14px 12px",
                    border:`2px solid ${isActive?C.gold:C.cardBord}`,
                    background:isActive?(darkMode?"rgba(200,164,74,.08)":"#FFFDF0"):(darkMode?"rgba(255,255,255,.02)":"#FAFAFA"),
                    cursor:"pointer", transition:"all .15s", position:"relative" }}>
                  {/* Rank badge */}
                  <div style={{ position:"absolute", top:10, right:10, width:22, height:22, borderRadius:"50%",
                    background:i===0?C.gold:darkMode?"#1E2840":"#E5E7EB",
                    color:i===0?"#0D1B2A":C.textMut, fontSize:10, fontWeight:800, fontFamily:FONT,
                    display:"flex", alignItems:"center", justifyContent:"center" }}>
                    {i+1}
                  </div>
                  <div style={{ fontSize:11, fontWeight:700, color:isActive?C.gold:C.textPri, fontFamily:FONT, marginBottom:2 }}>{tc.term.short}</div>
                  <div style={{ fontSize:9.5, color:C.textMut, fontFamily:FONT, marginBottom:10 }}>{tc.term.pipeline}</div>

                  {/* Cheapest landed cost */}
                  <div style={{ fontSize:20, fontWeight:900, color:C.textPri, fontFamily:FONT, lineHeight:1, marginBottom:4 }}>
                    ${cheapest.toFixed(4)}
                  </div>
                  <div style={{ fontSize:9.5, color:C.textSec, fontFamily:FONT, marginBottom:10 }}>
                    {i===0 ? "Best price today" : `+$${vsFirst.toFixed(4)} vs best`}
                  </div>

                  {/* Contract vs Spot mini comparison */}
                  <div style={{ display:"flex", flexDirection:"column", gap:4, marginBottom:10 }}>
                    {[
                      { label:"Contract", val:tc.contractLanded, isWinner:tc.cheaper==="contract" },
                      { label:"Spot",     val:tc.spotLanded,     isWinner:tc.cheaper==="spot" },
                    ].map(row=>(
                      <div key={row.label} style={{ display:"flex", alignItems:"center", gap:6 }}>
                        <div style={{ width:4, height:4, borderRadius:"50%", background:row.isWinner?cheapColor:C.cardBord, flexShrink:0 }}/>
                        <span style={{ fontSize:9.5, color:row.isWinner?cheapColor:C.textMut, fontFamily:FONT, flex:1 }}>{row.label}</span>
                        <span style={{ fontSize:10, fontWeight:row.isWinner?700:400, color:row.isWinner?C.textPri:C.textMut, fontFamily:FONT }}>${row.val.toFixed(4)}</span>
                      </div>
                    ))}
                  </div>

                  {/* Mini cost bar */}
                  <div style={{ height:4, background:C.cardBord, borderRadius:2, overflow:"hidden" }}>
                    <div style={{ height:"100%", width:`${(cheapest/termCards[termCards.length-1].contractLanded)*100}%`, background:i===0?C.gold:GRADE_COL, borderRadius:2 }}/>
                  </div>

                  {/* Action pill */}
                  <div style={{ marginTop:10, padding:"4px 0", textAlign:"center", borderRadius:6,
                    background:tc.cheaper==="spot"?(darkMode?"rgba(34,197,94,.1)":"#F0FDF4"):(darkMode?"rgba(200,164,74,.1)":"#F8FAFB"),
                    border:`1px solid ${cheapColor}30`, fontSize:10, fontWeight:700, color:cheapColor, fontFamily:FONT }}>
                    {cheapLabel}  ·  saves ${tc.delta.toFixed(4)}/gal
                  </div>
                </div>
              );
            })}
          </div>
        </div>

        {/*  ALL SUPPLY OPTIONS  */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:18 }}>
          <div style={{ display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:4 }}>
            <div>
              <div style={{ fontSize:13, fontWeight:700, color:C.textPri, fontFamily:FONT }}>All Supply Options — {selectedGrade} · Every path to your tank</div>
              <div style={{ fontSize:10.5, color:C.textSec, marginTop:2, fontFamily:FONT }}>Colonial · Plantation · Marine · Truck — ranked by best spot landed cost. Lead time and grade availability vary.</div>
            </div>
            <div style={{ display:"flex", gap:8 }}>
              {Object.entries(ALT_SUPPLY_TYPES).map(([k,v])=>(
                <div key={k} style={{ display:"flex", alignItems:"center", gap:5, fontSize:10.5, color:C.textSec, fontFamily:FONT }}>
                  <span>{v.icon}</span><span>{v.label}</span>
                </div>
              ))}
            </div>
          </div>

          {/* Colonial row first, then alt supply sorted by spot landed */}
          {(()=>{
            const allRows = [];
            // Colonial terminals
            TERMINALS.forEach(t => {
              const r = RACK_PRICES[t.id][selectedGrade];
              const d = CONTRACT_DIFF[t.id][selectedGrade];
              const fr = FREIGHT[t.id];
              const spotL = r + SPOT_ADDER + fr + stateTax + FED_TAX;
              const contractL = r + d + fr + stateTax + FED_TAX;
              const win = COLONIAL.terminalWindows[t.id];
              allRows.push({
                id:t.id, name:t.name, short:t.short,
                type:"pipeline", pipelineName:"Colonial",
                icon:"", typeColor:"#3B82F6",
                spotLanded:spotL, contractLanded:contractL,
                cheaper:spotL < contractL ? "spot" : "contract",
                rack:r, leadDays:3,
                status:COLONIAL.status,
                windowOpen:win?.daysToWindow===0,
                daysToWindow:win?.daysToWindow,
                allocationActive:COLONIAL.allocationPct!==null,
                hasGrade:true,
                nominationDeadline:COLONIAL.nominationDeadline,
                weatherRisk:null,
                isColonial:true,
                isActive:t.id===selectedTerminal,
              });
            });
            // Alt supply points
            ALT_SUPPLY_POINTS.forEach(sp => {
              if (!sp.availableGrades.includes(selectedGrade)) return;
              const c = altLandedCost(sp, selectedGrade, stateTax);
              if (!c) return;
              const tc = ALT_SUPPLY_TYPES[sp.type];
              allRows.push({
                id:sp.id, name:sp.name, short:sp.short,
                type:sp.type, pipelineName:sp.pipeline||sp.type,
                icon:tc.icon, typeColor:tc.color,
                spotLanded:c.spot, contractLanded:c.contract,
                cheaper:c.contract&&c.contract<c.spot?"contract":"spot",
                rack:c.rack, leadDays:sp.leadDays,
                status:sp.status,
                windowOpen:sp.cycleWindowOpen,
                daysToWindow:sp.leadDays,
                allocationActive:sp.allocationActive,
                hasGrade:true,
                nominationDeadline:sp.nominationDeadline,
                weatherRisk:sp.weatherRisk||null,
                notes:sp.notes,
                bestFor:sp.bestFor,
                isColonial:false,
                isActive:false,
              });
            });
            // Sort by spot landed cost
            allRows.sort((a,b) => a.spotLanded - b.spotLanded);
            const bestSpot = allRows[0]?.spotLanded || 0;

            return (
              <div style={{ display:"flex", flexDirection:"column", gap:1, marginTop:12 }}>
                {/* Column headers */}
                <div style={{ display:"grid", gridTemplateColumns:"24px 220px 80px 90px 90px 90px 80px 80px 90px 1fr", gap:"0 10px", padding:"5px 10px", background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC", borderRadius:6, marginBottom:4 }}>
                  {["","Supply Point","Type","Spot Landed","Contract","Rack","Freight","Lead Time","Window/Status","Notes"].map((h,i)=>(
                    <div key={i} style={{ fontSize:9, color:C.textMut, fontWeight:700, textTransform:"uppercase", letterSpacing:.4, fontFamily:FONT, textAlign:["Spot Landed","Contract","Rack","Freight"].includes(h)?"right":"left" }}>{h}</div>
                  ))}
                </div>

                {allRows.map((row, ri) => {
                  const isBest = ri === 0;
                  const vsBase = row.spotLanded - bestSpot;
                  const rowBg = row.isActive
                    ? (darkMode?"rgba(200,164,74,.08)":"#FFFDF0")
                    : isBest
                    ? (darkMode?"rgba(34,197,94,.06)":"#F0FDF4")
                    : ri%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)");

                  return (
                    <div key={row.id}
                      onClick={()=>{ if(row.isColonial) setSelectedTerminal(row.id); }}
                      style={{ display:"grid", gridTemplateColumns:"24px 220px 80px 90px 90px 90px 80px 80px 90px 1fr", gap:"0 10px", padding:"9px 10px", borderRadius:6, background:rowBg, cursor:row.isColonial?"pointer":"default", alignItems:"center", border:`1px solid ${row.isActive?C.gold:isBest?C.green+"40":"transparent"}`, marginBottom:1 }}>

                      {/* Rank */}
                      <div style={{ fontSize:10, fontWeight:700, color:isBest?C.green:C.textMut, fontFamily:FONT, textAlign:"center" }}>{isBest?"":ri+1}</div>

                      {/* Name */}
                      <div>
                        <div style={{ display:"flex", alignItems:"center", gap:5 }}>
                          <span style={{ fontSize:14 }}>{row.icon}</span>
                          <span style={{ fontSize:11, fontWeight:row.isActive||isBest?700:500, color:row.isActive?C.gold:isBest?C.green:C.textPri, fontFamily:FONT }}>{row.name}</span>
                          {isBest && <span style={{ fontSize:9, background:C.green, color:"#fff", borderRadius:8, padding:"1px 5px", fontWeight:700, fontFamily:FONT }}>BEST</span>}
                        </div>
                        <div style={{ fontSize:9.5, color:C.textMut, marginTop:1, fontFamily:FONT }}>{row.pipelineName} · {row.short}</div>
                      </div>

                      {/* Type badge */}
                      <div>
                        <span style={{ fontSize:9.5, fontWeight:700, padding:"2px 7px", borderRadius:8, background:`${row.typeColor}18`, color:row.typeColor, border:`1px solid ${row.typeColor}30`, fontFamily:FONT }}>
                          {ALT_SUPPLY_TYPES[row.type]?.label||row.type}
                        </span>
                      </div>

                      {/* Spot landed */}
                      <div style={{ textAlign:"right" }}>
                        <div style={{ fontSize:12, fontWeight:800, color:isBest?C.green:C.textPri, fontFamily:FONT }}>${row.spotLanded.toFixed(4)}</div>
                        {!isBest && <div style={{ fontSize:9.5, color:C.red, fontFamily:FONT }}>+${vsBase.toFixed(4)}</div>}
                      </div>

                      {/* Contract landed */}
                      <div style={{ textAlign:"right", fontSize:11, color:row.contractLanded?C.textSec:C.textMut, fontFamily:FONT }}>
                        {row.contractLanded ? `$${row.contractLanded.toFixed(4)}` : "—"}
                      </div>

                      {/* Rack */}
                      <div style={{ textAlign:"right", fontSize:11, color:C.textSec, fontFamily:FONT }}>${row.rack.toFixed(4)}</div>

                      {/* Freight */}
                      <div style={{ textAlign:"right", fontSize:11, color:C.textSec, fontFamily:FONT }}>
                        ${(row.spotLanded - row.rack - SPOT_ADDER - stateTax - FED_TAX).toFixed(4)}
                      </div>

                      {/* Lead time */}
                      <div style={{ textAlign:"center" }}>
                        <span style={{ fontSize:11, fontWeight:700, color:row.leadDays<=2?C.green:row.leadDays<=5?C.amber:C.textSec, fontFamily:FONT }}>
                          {row.leadDays}d
                        </span>
                      </div>

                      {/* Window / Status */}
                      <div>
                        {row.type==="pipeline" ? (
                          <span style={{ fontSize:9.5, fontWeight:700, padding:"2px 7px", borderRadius:8, fontFamily:FONT,
                            background:row.windowOpen?(darkMode?"rgba(34,197,94,.15)":"#F0FDF4"):(darkMode?"rgba(107,114,128,.12)":"#F8FAFC"),
                            color:row.windowOpen?C.green:C.textMut,
                            border:`1px solid ${row.windowOpen?C.green+"40":C.cardBord}` }}>
                            {row.windowOpen ? " Window Open" : `${row.daysToWindow}d to window`}
                          </span>
                        ) : (
                          <span style={{ fontSize:9.5, fontWeight:700, padding:"2px 7px", borderRadius:8, fontFamily:FONT,
                            background:row.status==="AVAILABLE"?(darkMode?"rgba(14,165,233,.12)":"#F0F9FF"):(darkMode?"rgba(251,191,36,.12)":"#F8FAFB"),
                            color:row.status==="AVAILABLE"?"#0EA5E9":C.amber,
                            border:`1px solid ${row.status==="AVAILABLE"?"#0EA5E9":C.amber}30` }}>
                            {row.status}
                          </span>
                        )}
                        {row.allocationActive && <span style={{ marginLeft:4, fontSize:9, color:C.amber, fontWeight:700 }}>ALLOC</span>}
                        {row.weatherRisk==="High" && <span style={{ marginLeft:4, fontSize:9 }} title={row.weatherRisk}></span>}
                      </div>

                      {/* Notes / best for */}
                      <div style={{ fontSize:9.5, color:C.textMut, lineHeight:1.35, fontFamily:FONT, overflow:"hidden" }}>
                        {row.bestFor
                          ? <span>Best for: <strong style={{ color:C.textSec }}>{row.bestFor.slice(0,3).join(", ")}</strong></span>
                          : row.notes?.substring(0,60)+"…" }
                      </div>
                    </div>
                  );
                })}
              </div>
            );
          })()}
        </div>

        {/*  CONTRACT DETAILS + ALERTS row  */}
        <div style={{ display:"flex", gap:14 }}>
          <div style={{ flex:1, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
            <div style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT, marginBottom:10 }}>Contract Details — {term?.name}</div>
            <div style={{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:"0 24px" }}>
              {[
                { label:"Primary Supplier", val:term?.supplier },
                { label:"Pipeline",         val:term?.pipeline },
                { label:"Volume Commitment",val:"850K gal/month" },
                { label:"Min Commitment",   val:"780K gal/month" },
                { label:"Contract Expiry",  val:"Dec 31, 2025" },
                { label:"Month-to-Date Pace",   val:"91.4% (712K gal)" },
                { label:"Colonial Tariff (Gas)",  val:`$${COLONIAL.tariffs[selectedTerminal]?.gasoline?.toFixed(4)||"—"}/gal` },
                { label:"Colonial Tariff (Dist)", val:`$${COLONIAL.tariffs[selectedTerminal]?.distillate?.toFixed(4)||"—"}/gal` },
                { label:"Next Lift Window",        val:COLONIAL.terminalWindows[selectedTerminal]?.daysToWindow===0?"Open Now":`In ${COLONIAL.terminalWindows[selectedTerminal]?.daysToWindow} days` },
              ].map(item=>(
                <div key={item.label} style={{ display:"flex", justifyContent:"space-between", padding:"5px 0", borderBottom:`1px solid ${C.cardBord}` }}>
                  <span style={{ fontSize:10.5, color:C.textSec }}>{item.label}</span>
                  <span style={{ fontSize:10.5, fontWeight:600, color:C.textPri, fontFamily:FONT }}>{item.val}</span>
                </div>
              ))}
            </div>
            <div style={{ marginTop:10 }}>
              <div style={{ display:"flex", justifyContent:"space-between", marginBottom:4 }}>
                <span style={{ fontSize:10, color:C.textSec }}>April commitment pace</span>
                <span style={{ fontSize:11, fontWeight:700, color:C.green, fontFamily:FONT }}>91.4%</span>
              </div>
              <InvBar pct={0.914} color={C.green} C={C}/>
              <div style={{ fontSize:9.5, color:C.textMut, marginTop:6 }}>68K gal remaining to meet minimum · 18 days left</div>
            </div>
          </div>
          <div style={{ width:280, flexShrink:0, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
            <div style={{ fontSize:11, fontWeight:700, color:C.textPri, fontFamily:FONT, marginBottom:10 }}> Market Alerts</div>
            {[
              { msg:`SEL rack up +$0.0124 since yesterday open — monitor for further moves`, level:"warn" },
              { msg:`Colonial Line 1 at ${COLONIAL.line1Capacity}% · Line 2 at ${COLONIAL.line2Capacity}% · ${COLONIAL.status==="NORMAL"?"Full flow normal — spot sourcing viable":"Constrained — contract volume preferred"}`, level:COLONIAL.line1Capacity>=97?"info":"warn" },
              { msg:`Nomination deadline: ${COLONIAL.nominationDeadline} — submit lifts before cutoff`, level:"warn" },
              { msg:`Spot at ${term?.short} $${deltaCPG.toFixed(4)}/gal ${spotIsCheaper?"cheaper than":"more expensive than"} contract on ${selectedGrade}`, level:spotIsCheaper&&!SPOT_CONSTRAINED?"good":"info" },
              { msg:`CLT window open now — ${COLONIAL.terminalWindows.charlotte.windowLen}-day lift window active, optimal timing`, level:"good" },
            ].map((alert, i)=>(
              <div key={i} style={{ padding:"8px 10px", borderRadius:6, marginBottom:6, background:alert.level==="warn"?(darkMode?"rgba(251,191,36,.08)":"#F8FAFB"):alert.level==="good"?(darkMode?"rgba(34,197,94,.08)":"#F0FDF4"):(darkMode?"rgba(59,130,246,.08)":"#EFF6FF"), border:`1px solid ${alert.level==="warn"?C.amber+"40":alert.level==="good"?C.green+"40":C.blue+"40"}` }}>
                <div style={{ fontSize:10.5, color:alert.level==="warn"?C.amber:alert.level==="good"?C.green:C.blue, lineHeight:1.4 }}>{alert.msg}</div>
              </div>
            ))}
          </div>
        </div>

      </div>
    );
  };

  //  Tab: Today's Best Buy
  //  The "where's the money today" screen — cheapest supplier for each
  //  terminal × grade combination, with savings vs next-best. Procurement
  //  people open this first thing every morning to decide which suppliers
  //  to prioritize for today's dispatch.
  //
  //  Plus is special: it's blended from Reg and Prem, so it doesn't have
  //  a single supplier. We show Plus cells as derived (blended cost from
  //  the cheapest Reg + cheapest Prem at that terminal), with a subtle
  //  "BLENDED" label so buyers understand the math.
  const renderBestBuy = () => {
    const FONT = "Arial,sans-serif";
    // Typical daily volume at each terminal — used to project daily savings.
    // Hand-set from the STORES territory volumes; in production this would
    // come from actual lift history.
    const TYPICAL_DAILY_VOL = {
      selma: 280_000, apex: 220_000, charlotte: 240_000, richmond: 190_000,
      atlanta: 310_000, macon: 200_000, bainbridge: 140_000, birmingham: 260_000,
      jacksonville: 170_000, tampa: 150_000,
    };
    const MEANINGFUL_SAVINGS_CPG = 0.005; // $/gal — below this, just noise

    // For each terminal × grade, compute the ranked supplier options.
    // Plus is derived (50/50 of cheapest Reg + cheapest Prem).
    const cells = {};
    TERMINALS.forEach(t => {
      cells[t.id] = {};
      const suppliers = SUPPLIERS_BY_TERMINAL[t.id] || [];
      ["Regular","Premium","Diesel"].forEach(g => {
        const options = suppliers.map(s => {
          const cost = supplierCostPerGal(s, g);
          return {
            supplier: s,
            rack: cost.rack,
            diff: cost.isSpot ? 0 : cost.diff,
            spotPremium: cost.isSpot ? cost.premium : 0,
            isSpot: cost.isSpot,
            contractStatus: s.contractStatus,
            landed: cost.total, // rack + diff/premium, excludes freight/tax (same for all suppliers at this terminal)
          };
        }).sort((a,b) => a.landed - b.landed);
        cells[t.id][g] = options;
      });
      // Plus = blended from cheapest Reg + cheapest Prem
      const cheapestReg = cells[t.id].Regular[0];
      const cheapestPrem = cells[t.id].Premium[0];
      if (cheapestReg && cheapestPrem) {
        const blendedLanded = 0.5 * cheapestReg.landed + 0.5 * cheapestPrem.landed;
        cells[t.id].Plus = {
          isBlended: true,
          regSupplier: cheapestReg.supplier,
          premSupplier: cheapestPrem.supplier,
          regLanded: cheapestReg.landed,
          premLanded: cheapestPrem.landed,
          landed: blendedLanded,
        };
      }
    });

    // Aggregate savings — for each cell compare best vs primary-supplier option.
    // Sum "savings captured if we route to the best" across all terminals × grades.
    let totalSavingsPerDay = 0;
    let spotCheaperCount = 0;
    let meaningfulSavingsCount = 0;
    TERMINALS.forEach(t => {
      ["Regular","Premium","Diesel"].forEach(g => {
        const opts = cells[t.id][g];
        if (!opts || opts.length < 2) return;
        const best = opts[0];
        const primary = opts.find(o => o.contractStatus === "primary") || opts[1];
        const savingsCpg = primary.landed - best.landed;
        // Approximate daily volume for this grade at this terminal — rough
        // split: 60% Reg, 20% Prem, 20% Diesel (Plus is derived from Reg+Prem)
        const gradeShare = g === "Regular" ? 0.55 : g === "Premium" ? 0.20 : 0.25;
        const dailyVol = (TYPICAL_DAILY_VOL[t.id] || 200_000) * gradeShare;
        if (savingsCpg > 0) {
          totalSavingsPerDay += savingsCpg * dailyVol;
        }
        if (savingsCpg >= MEANINGFUL_SAVINGS_CPG) meaningfulSavingsCount++;
        if (best.isSpot) spotCheaperCount++;
      });
    });

    // Helper — pill color for a cell's best option
    const cellPillStyle = (best, savingsCpg) => {
      if (best.isSpot) return {
        color:"#EA580C",
        bg: darkMode?"rgba(234,88,12,.12)":"#FFF7ED",
        border:"#EA580C",
      };
      if (savingsCpg >= MEANINGFUL_SAVINGS_CPG) return {
        color:"#16A34A",
        bg: darkMode?"rgba(22,163,74,.12)":"#F0FDF4",
        border:"#16A34A",
      };
      return {
        color: C.textSec,
        bg: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
        border: C.cardBord,
      };
    };

    // ── 7-day price trend per terminal × grade from RACK_HISTORY ──────────
    const sevenDayTrend = {};
    TERMINALS.forEach(t => {
      sevenDayTrend[t.id] = {};
      GRADES.forEach(g => {
        const hist = RACK_HISTORY[t.id]?.[g];
        if (hist && hist.length >= 8) {
          sevenDayTrend[t.id][g] = hist[hist.length-1] - hist[hist.length-8];
        } else {
          sevenDayTrend[t.id][g] = 0;
        }
      });
    });

    // ── Portfolio average landed cost per grade (for heatmap) ─────────────
    const portfolioAvg = {};
    ["Regular","Premium","Diesel"].forEach(g => {
      const vals = TERMINALS.map(t => cells[t.id]?.[g]?.[0]?.landed).filter(Boolean);
      portfolioAvg[g] = vals.reduce((a,b)=>a+b,0) / (vals.length || 1);
    });

    // ── MTD lift pct per supplier id from TERMINAL_SUPPLIERS ─────────────
    const mtdLiftPct = {};
    TERMINAL_SUPPLIERS.forEach(s => {
      if (s.monthlyCommit > 0) {
        mtdLiftPct[s.id] = s.liftedMTD / s.monthlyCommit;
      }
    });

    // ── Top single opportunity: volume × savings/gal ─────────────────────
    let topOpp = null;
    TERMINALS.forEach(t => {
      ["Regular","Premium","Diesel"].forEach(g => {
        const opts = cells[t.id]?.[g];
        if (!opts || opts.length < 2) return;
        const best = opts[0];
        const primary = opts.find(o => o.contractStatus==="primary") || opts[1];
        const savingsCpg = primary.landed - best.landed;
        const gradeShare = g==="Regular"?0.55:g==="Premium"?0.20:0.25;
        const dailyVol = (TYPICAL_DAILY_VOL[t.id]||200000) * gradeShare;
        const dailySavings = savingsCpg * dailyVol;
        if (!topOpp || dailySavings > topOpp.dailySavings) {
          topOpp = { t, g, best, savingsCpg, dailySavings, dailyVol };
        }
      });
    });

    // ── Apply bestBuyFilter to cells ──────────────────────────────────────
    const filteredCell = (tId, g) => {
      const opts = cells[tId]?.[g] || [];
      if (bestBuyFilter === "spot") return opts.filter(o => o.isSpot);
      if (bestBuyFilter === "contract") return opts.filter(o => !o.isSpot);
      return opts;
    };

    // ── Winner per terminal (which supplier wins most grades) ─────────────
    const terminalWinner = {};
    TERMINALS.forEach(t => {
      const wins = {};
      ["Regular","Premium","Diesel"].forEach(g => {
        const best = filteredCell(t.id, g)[0];
        if (best) wins[best.supplier.short] = (wins[best.supplier.short]||0) + 1;
      });
      const top = Object.entries(wins).sort((a,b)=>b[1]-a[1])[0];
      terminalWinner[t.id] = top ? { short: top[0], wins: top[1] } : null;
    });

    return (
      <div style={{display:"flex", flexDirection:"column", gap:14}}>
        {/* Header banner — aggregate savings */}
        <div style={{
          background: totalSavingsPerDay > 1000 ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4") : C.cardBg,
          border: `1px solid ${totalSavingsPerDay > 1000 ? "rgba(22,163,74,.35)" : C.cardBord}`,
          borderRadius:10, padding:"14px 18px",
        }}>
          <div style={{display:"flex", justifyContent:"space-between", alignItems:"flex-start", gap:12, flexWrap:"wrap"}}>
            <div>
              <div style={{fontSize:11, fontWeight:800, letterSpacing:.6, textTransform:"uppercase",
                color: totalSavingsPerDay > 1000 ? "#16A34A" : C.textMut, fontFamily:FONT}}>
                {totalSavingsPerDay > 0
                  ? `Save $${Math.round(totalSavingsPerDay).toLocaleString()}/day at cheapest supplier`
                  : "Primaries cheapest today — no savings available"}
              </div>
              <div style={{fontSize:11.5, color:C.textSec, marginTop:4, fontFamily:FONT}}>
                {meaningfulSavingsCount}/18 combos beat pick by &gt;$0.005/gal
                {spotCheaperCount > 0 && <> · <strong style={{color:"#EA580C"}}>spot cheaper at {spotCheaperCount}</strong></>}
              </div>
            </div>
            <div style={{display:"flex", gap:10, alignItems:"flex-start", flexWrap:"wrap"}}>
              {/* Top opportunity callout */}
              {topOpp && (
                <div style={{
                  padding:"8px 14px", borderRadius:8,
                  background: darkMode?"rgba(22,163,74,.08)":"#F0FDF4",
                  border:`1px solid rgba(22,163,74,.35)`, textAlign:"right",
                }}>
                  <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.4, textTransform:"uppercase"}}>Top opportunity</div>
                  <div style={{fontSize:13, fontWeight:900, color:"#16A34A", fontFamily:FONT, lineHeight:1.1, marginTop:2}}>
                    {topOpp.t.short} · {topOpp.g}
                  </div>
                  <div style={{fontSize:9.5, color:"#16A34A", fontWeight:700, marginTop:2}}>
                    ${Math.round(topOpp.dailySavings).toLocaleString()}/day · ${topOpp.savingsCpg.toFixed(4)}/gal
                  </div>
                  <div style={{fontSize:9, color:C.textMut, marginTop:1}}>
                    route to {topOpp.best.supplier.short}{topOpp.best.isSpot?" (spot)":""}
                  </div>
                </div>
              )}
              {/* Monthly savings tile */}
              <div style={{
                padding:"8px 14px", borderRadius:8,
                background: darkMode?"rgba(200,164,74,.10)":"#FFF9E6",
                border:`1px solid ${C.gold}40`, textAlign:"right",
              }}>
                <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.4, textTransform:"uppercase"}}>
                  Monthly savings potential
                </div>
                <div style={{fontSize:22, fontWeight:900, color:C.gold, fontFamily:FONT, lineHeight:1}}>
                  ${Math.round(totalSavingsPerDay * 30 / 1000).toLocaleString()}K
                </div>
                <div style={{fontSize:9, color:C.textMut, marginTop:2}}>at current rack spreads</div>
              </div>
            </div>
          </div>
        </div>

        {/* Filter toggle + legend */}
        <div style={{display:"flex", alignItems:"center", gap:10, flexWrap:"wrap"}}>
          <div style={{display:"flex", gap:3, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:7, padding:3}}>
            {[["all","All Sources"],["contract","Contract Only"],["spot","Spot Only"]].map(([val,label])=>(
              <button key={val} onClick={()=>setBestBuyFilter(val)}
                style={{padding:"4px 12px", borderRadius:5, border:"none", cursor:"pointer", fontFamily:FONT,
                  fontSize:10, fontWeight:bestBuyFilter===val?700:400,
                  background:bestBuyFilter===val?"#0D1B2A":"transparent",
                  color:bestBuyFilter===val?C.gold:C.textSec, transition:"all .12s"}}>
                {label}
              </button>
            ))}
          </div>
          <div style={{display:"flex", gap:12, fontSize:9, color:C.textMut, fontFamily:FONT, alignItems:"center"}}>
            <span style={{display:"flex", alignItems:"center", gap:4}}><span style={{color:"#16A34A", fontWeight:800}}>↑</span> price rising this week</span>
            <span style={{display:"flex", alignItems:"center", gap:4}}><span style={{color:"#DC2626", fontWeight:800}}>↓</span> price falling</span>
            <span style={{display:"flex", alignItems:"center", gap:4}}><span style={{color:"#DC2626", fontSize:8}}>●</span> above portfolio avg</span>
            <span style={{display:"flex", alignItems:"center", gap:4}}><span style={{color:"#16A34A", fontSize:8}}>●</span> below portfolio avg</span>
          </div>
        </div>

        {/* Grid — terminals down, grades across */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden"}}>
          {/* Column headers */}
          <div style={{
            display:"grid",
            gridTemplateColumns:"180px 1fr 1fr 1fr 1fr",
            gap:1, padding:0,
            background: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
            borderBottom:`1px solid ${C.cardBord}`,
          }}>
            <div style={{padding:"10px 14px", fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", fontFamily:FONT}}>
              Terminal
            </div>
            {["Regular","Plus","Premium","Diesel"].map(g => (
              <div key={g} style={{padding:"10px 14px", fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", fontFamily:FONT, textAlign:"left"}}>
                {g}
              </div>
            ))}
          </div>

          {TERMINALS.map((t, ti) => {
            const isLastTerm = ti === TERMINALS.length - 1;
            return (
              <React.Fragment key={t.id}>
                {/* Terminal row — 4 grade cells */}
                <div style={{
                  display:"grid",
                  gridTemplateColumns:"180px 1fr 1fr 1fr 1fr",
                  gap:1,
                  background: darkMode?"rgba(255,255,255,.02)":"#FFFFFF",
                  borderBottom: !isLastTerm ? `1px solid ${C.cardBord}` : "none",
                }}>
                  {/* Terminal label */}
                  <div style={{padding:"14px", display:"flex", flexDirection:"column", justifyContent:"center", gap:2, borderRight:`1px solid ${C.cardBord}`}}>
                    <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
                      <ZoneBadge terminalId={t.id}/> {t.short} · {t.name.split(",")[0]}
                    </div>
                    <div style={{fontSize:9.5, color:C.textMut}}>
                      {((TYPICAL_DAILY_VOL[t.id]||0)/1000).toFixed(0)}K gal/day typical
                    </div>
                    {terminalWinner[t.id] && (() => {
                      const winSupplier = TERMINAL_SUPPLIERS.find(s => s.short === terminalWinner[t.id].short);
                      return (
                        <div style={{marginTop:4, fontSize:8.5, color:C.textSec, fontFamily:FONT, display:"flex", alignItems:"center", gap:4}}>
                          {winSupplier
                            ? <SupplierLogo supplierName={winSupplier.name} supplierShort={winSupplier.short} size={14}/>
                            : <span style={{fontWeight:700, color:C.gold}}>{terminalWinner[t.id].short}</span>}
                          {" wins "}{terminalWinner[t.id].wins}/3 grades
                        </div>
                      );
                    })()}
                  </div>
                  {/* Grade cells */}
                  {["Regular","Plus","Premium","Diesel"].map(g => {
                    const cellKey = `${t.id}:${g}`;
                    const isExpanded = bestBuyExpanded === cellKey;
                    // Plus cell is special (blended)
                    if (g === "Plus") {
                      const plus = cells[t.id].Plus;
                      if (!plus) return <div key={g} style={{padding:"14px", borderRight: g !== "Diesel" ? `1px solid ${C.cardBord}` : "none"}}/>;
                      return (
                        <div key={g}
                          style={{
                            padding:"10px 14px", borderRight: g !== "Diesel" ? `1px solid ${C.cardBord}` : "none",
                            background: darkMode?"rgba(13,148,136,.04)":"#F0FDFA",
                          }}>
                          <div style={{display:"flex", alignItems:"baseline", gap:5, marginBottom:4}}>
                            <span style={{
                              fontSize:8.5, fontWeight:800, padding:"1px 5px", borderRadius:3,
                              background: darkMode?"rgba(13,148,136,.12)":"#F0FDFA",
                              color:"#0D9488", letterSpacing:.4, border:"1px solid rgba(13,148,136,.3)",
                            }}>
                              BLENDED
                            </span>
                          </div>
                          <div style={{fontSize:14, fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                            ${plus.landed.toFixed(4)}
                          </div>
                          <div style={{fontSize:9, color:C.textMut, marginTop:3, lineHeight:1.4}}>
                            ½ {plus.regSupplier.short} Reg (${plus.regLanded.toFixed(4)})<br/>
                            ½ {plus.premSupplier.short} Prem (${plus.premLanded.toFixed(4)})
                          </div>
                        </div>
                      );
                    }
                    // Regular / Premium / Diesel — use filteredCell
                    const opts = filteredCell(t.id, g);
                    if (!opts || opts.length === 0) return (
                      <div key={g} style={{padding:"10px 14px", borderRight: g !== "Diesel" ? `1px solid ${C.cardBord}` : "none",
                        display:"flex", alignItems:"center", justifyContent:"center"}}>
                        <span style={{fontSize:9.5, color:C.textMut, fontStyle:"italic"}}>
                          {bestBuyFilter==="spot"?"no spot":"no contract"}
                        </span>
                      </div>
                    );
                    const best = opts[0];
                    const secondBest = opts[1];
                    const savingsCpg = secondBest ? secondBest.landed - best.landed : 0;
                    const gradeShare = g === "Regular" ? 0.55 : g === "Premium" ? 0.20 : 0.25;
                    const dailyVol = (TYPICAL_DAILY_VOL[t.id] || 200_000) * gradeShare;
                    const dailySavings = savingsCpg * dailyVol;
                    const style = cellPillStyle(best, savingsCpg);
                    // Heatmap: deviation from portfolio average for this grade
                    const avg = portfolioAvg[g] || best.landed;
                    const deviation = best.landed - avg;
                    const heatAlpha = Math.min(0.08, Math.abs(deviation) / avg * 3);
                    const heatColor = deviation > 0.005 ? `rgba(220,38,38,${heatAlpha})` : deviation < -0.005 ? `rgba(22,163,74,${heatAlpha})` : "transparent";
                    // 7-day trend
                    const trend = sevenDayTrend[t.id]?.[g] || 0;
                    const trendUp = trend > 0.002;
                    const trendDown = trend < -0.002;
                    // MTD lift for this supplier
                    const suppMtd = mtdLiftPct[best.supplier.id];
                    return (
                      <div key={g}
                        onClick={()=>setBestBuyExpanded(isExpanded ? null : cellKey)}
                        style={{
                          padding:"10px 14px",
                          borderRight: g !== "Diesel" ? `1px solid ${C.cardBord}` : "none",
                          cursor:"pointer", transition:"background .12s",
                          background: isExpanded
                            ? (darkMode?"rgba(200,164,74,.06)":"#F8FAFB")
                            : heatColor || "transparent",
                        }}
                        onMouseEnter={e=>{ if (!isExpanded) e.currentTarget.style.background = darkMode?"rgba(255,255,255,.02)":"#FAFBFD"; }}
                        onMouseLeave={e=>{ e.currentTarget.style.background = isExpanded ? (darkMode?"rgba(200,164,74,.06)":"#F8FAFB") : (heatColor||"transparent"); }}
                        >
                        <div style={{display:"flex", alignItems:"center", gap:5, marginBottom:4}}>
                          {(() => {
                            const brand = supplierBrand(best.supplier.name);
                            return (
                              <span style={{
                                display:"inline-flex", alignItems:"center", gap:5,
                                fontSize:9, fontWeight:800, padding:"2px 6px 2px 3px", borderRadius:3,
                                background: `${brand.primary}20`,
                                color: brand.primary,
                                letterSpacing:.4, border:`1px solid ${brand.primary}50`,
                              }}>
                                <SupplierLogo supplierName={best.supplier.name} supplierShort={best.supplier.short} size={14}/>
                                {best.supplier.short}
                                {best.isSpot && <span style={{color:"#EA580C", fontWeight:800}}>·SPOT</span>}
                                {!best.isSpot && best.contractStatus === "secondary" && <span style={{opacity:.75}}>·2°</span>}
                              </span>
                            );
                          })()}
                          {opts.length > 1 && (
                            <span style={{fontSize:9, color:C.textMut}}>of {opts.length}</span>
                          )}
                          {/* 7-day trend arrow */}
                          {(trendUp || trendDown) && (
                            <span style={{fontSize:9, fontWeight:800, color: trendUp?"#DC2626":"#16A34A", marginLeft:2}} title={`${trendUp?"+":""}${trend.toFixed(4)}/gal vs 7 days ago`}>
                              {trendUp?"↑":"↓"}{Math.abs(trend).toFixed(3)}
                            </span>
                          )}
                          <span style={{marginLeft:"auto", fontSize:9, color:C.textMut}}>
                            {isExpanded ? "▾" : "▸"}
                          </span>
                        </div>
                        <div style={{fontSize:14, fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                          ${best.landed.toFixed(4)}
                        </div>
                        {savingsCpg > 0 ? (
                          <div style={{fontSize:9.5, color: savingsCpg >= MEANINGFUL_SAVINGS_CPG ? "#16A34A" : C.textMut, fontWeight: savingsCpg >= MEANINGFUL_SAVINGS_CPG ? 700 : 500, marginTop:3, fontFamily:"Arial,sans-serif"}}>
                            save ${savingsCpg.toFixed(4)}/gal
                            {dailySavings >= 100 && <span style={{color:"#16A34A"}}> · ${Math.round(dailySavings).toLocaleString()}/day</span>}
                          </div>
                        ) : (
                          <div style={{fontSize:9.5, color:C.textMut, marginTop:3}}>only option</div>
                        )}
                        {best.isSpot && (
                          <div style={{fontSize:8.5, color:"#EA580C", fontWeight:700, marginTop:3, letterSpacing:.3}}>
                            SPOT CHEAPER THAN CONTRACT
                          </div>
                        )}
                        {/* MTD lift badge */}
                        {suppMtd !== undefined && (
                          <div style={{marginTop:4, fontSize:8.5, fontFamily:"Arial,sans-serif",
                            color: suppMtd < 0.88 ? "#DC2626" : suppMtd > 1.05 ? "#F59E0B" : C.textMut}}>
                            MTD {(suppMtd*100).toFixed(0)}% of commit
                          </div>
                        )}
                      </div>
                    );
                  })}
                </div>

                {/* Expanded cell detail — full ranked list of suppliers at this terminal for chosen grade */}
                {bestBuyExpanded && bestBuyExpanded.startsWith(`${t.id}:`) && !bestBuyExpanded.endsWith(":Plus") && (() => {
                  const [, g] = bestBuyExpanded.split(":");
                  const opts = cells[t.id][g];
                  if (!opts) return null;
                  const best = opts[0];
                  return (
                    <div style={{
                      padding:"12px 16px",
                      background: darkMode?"rgba(200,164,74,.04)":"#F8FAFB",
                      borderTop:`1px solid ${C.cardBord}`,
                      borderBottom: !isLastTerm ? `1px solid ${C.cardBord}` : "none",
                    }}>
                      <div style={{fontSize:10, fontWeight:800, color:C.gold, letterSpacing:.5, textTransform:"uppercase", marginBottom:8}}>
                        {t.short} · {g} · {opts.length} supplier option{opts.length>1?"s":""}
                      </div>
                      <div style={{
                        display:"grid", gridTemplateColumns:"30px 1fr 90px 90px 90px 90px 90px 110px",
                        gap:8, padding:"6px 8px",
                        background: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
                        fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase",
                        borderRadius:5,
                        fontFamily:FONT,
                      }}>
                        <div>#</div>
                        <div>Supplier</div>
                        <div style={{textAlign:"right"}}>Rack</div>
                        <div style={{textAlign:"right"}}>+Diff/Spot</div>
                        <div style={{textAlign:"right"}}>Landed</div>
                        <div style={{textAlign:"right"}}>vs best</div>
                        <div style={{textAlign:"right"}}>MTD lift</div>
                        <div style={{textAlign:"center"}}>Action</div>
                      </div>
                      {opts.map((o, oi) => {
                        const isBest = oi === 0;
                        const delta = o.landed - best.landed;
                        const statusColor = o.contractStatus === "primary" ? "#16A34A"
                                          : o.contractStatus === "secondary" ? "#F4D398"
                                          : "#EA580C";
                        const mtdPct = o.supplier.monthlyCommit > 0
                          ? (o.supplier.liftedMTD / o.supplier.monthlyCommit) * 100
                          : null;
                        return (
                          <div key={o.supplier.id} style={{
                            display:"grid", gridTemplateColumns:"30px 1fr 90px 90px 90px 90px 90px 110px",
                            gap:8, padding:"8px", alignItems:"center",
                            background: isBest ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4") : "transparent",
                            borderRadius:5,
                            marginTop:4,
                            fontFamily:FONT,
                          }}>
                            <div style={{fontSize:11, fontWeight:800, color: isBest ? "#16A34A" : C.textMut}}>#{oi+1}</div>
                            <div style={{display:"flex", alignItems:"center", gap:8, minWidth:0}}>
                              <SupplierLogo supplierName={o.supplier.name} supplierShort={o.supplier.short} size={22}/>
                              <span style={{fontSize:11, fontWeight:700, color:C.textPri}}>{o.supplier.name}</span>
                              {(() => {
                                const brand = supplierBrand(o.supplier.name);
                                return (
                                  <span style={{
                                    fontSize:9, fontWeight:800, padding:"1px 5px", borderRadius:3,
                                    color: brand.primary, background: `${brand.primary}20`,
                                    border:`1px solid ${brand.primary}50`,
                                  }}>
                                    {o.supplier.short}
                                    {o.isSpot && <span style={{color:"#EA580C", fontWeight:800}}>·SPOT</span>}
                                    {!o.isSpot && o.contractStatus === "secondary" && <span style={{opacity:.75}}>·2°</span>}
                                  </span>
                                );
                              })()}
                              {isBest && (
                                <span style={{fontSize:8.5, fontWeight:800, color:"#16A34A", background:darkMode?"rgba(22,163,74,.15)":"#DCFCE7", padding:"1px 5px", borderRadius:3, letterSpacing:.4}}>
                                  BEST
                                </span>
                              )}
                            </div>
                            <div style={{textAlign:"right", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif"}}>
                              ${o.rack.toFixed(4)}
                            </div>
                            <div style={{textAlign:"right", fontSize:10.5, color: o.isSpot ? "#EA580C" : C.textSec, fontFamily:"Arial,sans-serif", fontWeight: o.isSpot ? 600 : 400}}>
                              ${(o.isSpot ? o.spotPremium : o.diff).toFixed(4)}
                            </div>
                            <div style={{textAlign:"right", fontSize:11, fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                              ${o.landed.toFixed(4)}
                            </div>
                            <div style={{textAlign:"right", fontSize:10.5, color: delta === 0 ? "#16A34A" : C.textMut, fontWeight: delta === 0 ? 700 : 400, fontFamily:"Arial,sans-serif"}}>
                              {delta === 0 ? "best" : `+$${delta.toFixed(4)}`}
                            </div>
                            <div style={{textAlign:"right", fontSize:10, color:C.textSec, fontFamily:"Arial,sans-serif"}}>
                              {mtdPct !== null ? `${Math.round(mtdPct)}% of commit` : "spot"}
                            </div>
                            <div style={{textAlign:"center"}}>
                              <button
                                onClick={(e)=>{
                                  e.stopPropagation();
                                  setPlanFilter({
                                    terminalId: t.id,
                                    grade: g,
                                    supplierShort: o.supplier.short,
                                    reason: "route-loads",
                                    message: `Routing ${g} loads to ${o.supplier.name} (${o.supplier.short}) at ${t.name} — ${isBest ? "lowest landed cost today" : `$${delta.toFixed(4)}/gal vs best`}`,
                                  });
                                  setActiveTab("plan");
                                  addToast(`Filtered to ${t.short} ${g} loads — route to ${o.supplier.short}`, "info");
                                }}
                                style={{
                                  padding:"4px 10px", borderRadius:5,
                                  background: isBest ? "#3E6387" : "transparent",
                                  color: isBest ? "#fff" : "#3E6387",
                                  border: isBest ? "none" : `1px solid #3E638760`,
                                  fontSize:10, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                                }}>
                                Route loads →
                              </button>
                            </div>
                          </div>
                        );
                      })}
                      <div style={{fontSize:9, color:C.textMut, marginTop:8, fontStyle:"italic", fontFamily:FONT}}>
                        Landed = rack + supplier diff/spot premium. Excludes freight (varies by store) and taxes. MTD lift shows contract-protection context: a supplier under-committed may deserve priority even when not cheapest.
                      </div>
                    </div>
                  );
                })()}
              </React.Fragment>
            );
          })}
        </div>

        {/* Methodology footer */}
        <div style={{
          padding:"10px 14px", borderRadius:8,
          background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
          border:`1px dashed ${C.cardBord}`,
          fontSize:10, color:C.textMut, lineHeight:1.5, fontFamily:FONT,
        }}>
          <strong style={{color:C.textSec}}>How to read this page:</strong> each cell shows the cheapest supplier at that terminal for that grade, landed cost per gallon (rack + contract differential or spot premium), and savings per gallon vs the next-cheapest option. "Meaningful" savings threshold is $0.005/gal — below that, dispatch operational cost usually exceeds the gain. <strong style={{color:"#EA580C"}}>Spot cheaper than contract</strong> signals short-term arbitrage opportunity but comes with allocation risk and may underlift contract commitments — cross-reference Contracts tab before acting. Daily savings assume typical terminal volume × grade share (55% Reg / 20% Prem / 25% Diesel). Plus is blended 50/50 from the cheapest Regular and cheapest Premium suppliers at each terminal.
        </div>
      </div>
    );
  };

  //  Tab: Contracts
  //  A procurement person's daily read: which contracts are going to hit their
  //  minimums, which are at risk, and how many gallons per day we need to lift
  //  to catch up. Uses TERMINAL_SUPPLIERS data (monthlyCommit, liftedMTD,
  //  contractExpiry, contractStatus). Spot-only suppliers are excluded since
  //  they have no commitment to track.
  const renderContracts = () => {
    const FONT = "Arial,sans-serif";
    // Realistic month-pace modeling: assume we're 22 days into a 30-day month.
    // In production this pulls from the actual calendar.
    const DAYS_IN_MONTH = 30;
    const DAYS_ELAPSED = 22;
    const DAYS_REMAINING = DAYS_IN_MONTH - DAYS_ELAPSED;
    // Assumed penalty on shortfall — typical primary contract. Secondary
    // contracts often have milder clauses, so we use a lower rate.
    const PENALTY_PRIMARY_PER_GAL = 0.02;
    const PENALTY_SECONDARY_PER_GAL = 0.008;

    // Build per-contract summary row. Skip spot-only (no commitment).
    const contractRows = TERMINAL_SUPPLIERS
      .filter(s => s.contractStatus !== "spot-only")
      .map(s => {
        const terminal = TERMINALS.find(t => t.id === s.terminalId);
        const commit = s.monthlyCommit || 0;
        const lifted = s.liftedMTD || 0;
        const shortfall = Math.max(0, commit - lifted);
        const pctLifted = commit > 0 ? lifted / commit : 0;
        // Projected EOM position: linear extrapolation from current pace.
        // If we're 22 days in and have lifted 1.68M of 2.4M commit, pace =
        // 1.68M / 22 = 76,363/day → 76,363 × 30 = 2.29M projected → 110K short.
        const dailyPace = lifted / DAYS_ELAPSED;
        const projectedEOM = dailyPace * DAYS_IN_MONTH;
        const projectedShortfall = Math.max(0, commit - projectedEOM);
        const projectedOverage = Math.max(0, projectedEOM - commit);
        const projectedPct = commit > 0 ? projectedEOM / commit : 0;
        // What daily lift rate is needed to catch up (0 if already on pace)
        const neededRemaining = Math.max(0, commit - lifted);
        const neededPerDay = DAYS_REMAINING > 0 ? neededRemaining / DAYS_REMAINING : 0;
        // Status classification
        const isAtRisk = projectedShortfall > commit * 0.02; // >2% projected short
        const isOverlifting = projectedOverage > commit * 0.05; // >5% over
        const isOnPace = !isAtRisk && !isOverlifting;
        // Penalty exposure in $
        const penaltyRate = s.contractStatus === "primary" ? PENALTY_PRIMARY_PER_GAL : PENALTY_SECONDARY_PER_GAL;
        const penaltyExposure = projectedShortfall * penaltyRate;
        // Days to expiry — parse the "Dec 31 2026" style string
        let daysToExpiry = null;
        if (s.contractExpiry) {
          const exp = new Date(s.contractExpiry);
          const now = new Date();
          daysToExpiry = Math.round((exp - now) / (1000*60*60*24));
        }
        const isRenewingSoon = daysToExpiry !== null && daysToExpiry >= 0 && daysToExpiry <= 90;
        return {
          supplier: s, terminal, commit, lifted, shortfall, pctLifted,
          dailyPace, projectedEOM, projectedShortfall, projectedOverage, projectedPct,
          neededPerDay, isAtRisk, isOverlifting, isOnPace, penaltyExposure,
          daysToExpiry, isRenewingSoon,
        };
      });

    // Aggregate stats for the top banner
    const totals = {
      count: contractRows.length,
      totalCommit: contractRows.reduce((a,r)=>a+r.commit,0),
      totalLifted: contractRows.reduce((a,r)=>a+r.lifted,0),
      atRisk: contractRows.filter(r=>r.isAtRisk).length,
      onPace: contractRows.filter(r=>r.isOnPace).length,
      overlifting: contractRows.filter(r=>r.isOverlifting).length,
      renewingSoon: contractRows.filter(r=>r.isRenewingSoon).length,
      totalPenaltyExposure: contractRows.reduce((a,r)=>a+r.penaltyExposure,0),
    };

    // Filter + sort
    let filtered = contractRows;
    if (contractFilter === "at-risk")     filtered = filtered.filter(r => r.isAtRisk);
    if (contractFilter === "on-pace")     filtered = filtered.filter(r => r.isOnPace);
    if (contractFilter === "renewing")    filtered = filtered.filter(r => r.isRenewingSoon);
    if (contractSort === "risk")      filtered = [...filtered].sort((a,b) => b.penaltyExposure - a.penaltyExposure);
    if (contractSort === "supplier")  filtered = [...filtered].sort((a,b) => a.supplier.name.localeCompare(b.supplier.name));
    if (contractSort === "expiry")    filtered = [...filtered].sort((a,b) => (a.daysToExpiry ?? 99999) - (b.daysToExpiry ?? 99999));
    if (contractSort === "terminal")  filtered = [...filtered].sort((a,b) => a.terminal.name.localeCompare(b.terminal.name));

    // Color helpers
    const statusPillColor = (r) => r.isAtRisk ? "#DC2626" : r.isOverlifting ? "#F59E0B" : "#16A34A";
    const statusPillBg = (r) => r.isAtRisk ? (darkMode?"rgba(220,38,38,.12)":"#FEF2F2")
                                : r.isOverlifting ? (darkMode?"rgba(245,158,11,.12)":"#F8FAFB")
                                : (darkMode?"rgba(22,163,74,.12)":"#F0FDF4");
    const statusPillText = (r) => r.isAtRisk ? "AT RISK" : r.isOverlifting ? "OVERLIFT" : "ON PACE";

    return (
      <div style={{display:"flex", flexDirection:"column", gap:14}}>
        {/* Header banner — portfolio summary */}
        <div style={{
          background: totals.atRisk > 0 ? (darkMode?"rgba(220,38,38,.06)":"#FEF7F7") : C.cardBg,
          border: `1px solid ${totals.atRisk > 0 ? "rgba(220,38,38,.35)" : C.cardBord}`,
          borderRadius:10, padding:"14px 18px",
        }}>
          <div style={{display:"flex", justifyContent:"space-between", alignItems:"flex-start", gap:12, flexWrap:"wrap"}}>
            <div>
              <div style={{fontSize:11, fontWeight:800, letterSpacing:.6, textTransform:"uppercase",
                color: totals.atRisk > 0 ? "#DC2626" : C.textMut, fontFamily:FONT}}>
                {totals.atRisk > 0
                  ? `${totals.atRisk} contract${totals.atRisk>1?"s":""} at risk · $${Math.round(totals.totalPenaltyExposure).toLocaleString()} penalty exposure`
                  : "All contracts on pace — no penalty exposure"}
              </div>
              <div style={{fontSize:11.5, color:C.textSec, marginTop:4, fontFamily:FONT}}>
                {totals.count} active contracts · {(totals.totalCommit/1_000_000).toFixed(1)}M gal committed · {(totals.totalLifted/1_000_000).toFixed(1)}M lifted MTD ({Math.round(totals.totalLifted/totals.totalCommit*100)}% of target)
              </div>
              <div style={{fontSize:10.5, color:C.textMut, marginTop:4, fontFamily:FONT}}>
                Day {DAYS_ELAPSED} of {DAYS_IN_MONTH} · {DAYS_REMAINING} days remaining
                {totals.renewingSoon > 0 && <> · <strong style={{color:C.gold}}>{totals.renewingSoon} renewing in &lt;90 days</strong></>}
              </div>
            </div>
            {/* Quick KPI tiles */}
            <div style={{display:"flex", gap:8, flexWrap:"wrap"}}>
              {[
                {label:"At risk", val:totals.atRisk, color:"#DC2626"},
                {label:"On pace", val:totals.onPace, color:"#16A34A"},
                {label:"Overlifting", val:totals.overlifting, color:"#F59E0B"},
                {label:"Renewing <90d", val:totals.renewingSoon, color:C.gold},
              ].map(kpi => (
                <div key={kpi.label} style={{
                  padding:"7px 11px", borderRadius:7,
                  background: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
                  border:`1px solid ${C.cardBord}`,
                  minWidth:72, textAlign:"center",
                }}>
                  <div style={{fontSize:16, fontWeight:900, color:kpi.color, fontFamily:FONT, lineHeight:1}}>
                    {kpi.val}
                  </div>
                  <div style={{fontSize:9, color:C.textMut, fontWeight:700, letterSpacing:.3, textTransform:"uppercase", marginTop:3}}>
                    {kpi.label}
                  </div>
                </div>
              ))}
            </div>
          </div>
        </div>

        {/* Filter + sort controls */}
        <div style={{display:"flex", gap:10, alignItems:"center", flexWrap:"wrap"}}>
          <div style={{display:"flex", gap:6}}>
            {[
              {id:"all",      label:`All (${totals.count})`},
              {id:"at-risk",  label:`At risk (${totals.atRisk})`},
              {id:"on-pace",  label:`On pace (${totals.onPace})`},
              {id:"renewing", label:`Renewing <90d (${totals.renewingSoon})`},
            ].map(f => (
              <button key={f.id} onClick={()=>setContractFilter(f.id)}
                style={{
                  padding:"5px 12px", borderRadius:6,
                  border:`1px solid ${contractFilter===f.id?C.gold:C.cardBord}`,
                  background: contractFilter===f.id ? (darkMode?"rgba(200,164,74,.12)":"#FFF9E6") : "transparent",
                  color: contractFilter===f.id ? C.gold : C.textSec,
                  fontSize:10.5, fontWeight: contractFilter===f.id?700:500,
                  cursor:"pointer", fontFamily:FONT,
                }}>
                {f.label}
              </button>
            ))}
          </div>
          <div style={{marginLeft:"auto", display:"flex", gap:6, alignItems:"center"}}>
            <span style={{fontSize:10.5, color:C.textMut, fontWeight:600}}>Sort:</span>
            <select value={contractSort} onChange={e=>setContractSort(e.target.value)}
              style={{
                padding:"5px 10px", borderRadius:6,
                border:`1px solid ${C.cardBord}`,
                background: darkMode?"rgba(255,255,255,.04)":"#fff",
                color:C.textPri, fontSize:10.5, cursor:"pointer", fontFamily:FONT,
              }}>
              <option value="risk">Penalty exposure (highest first)</option>
              <option value="supplier">Supplier A→Z</option>
              <option value="terminal">Terminal A→Z</option>
              <option value="expiry">Days to renewal (soonest first)</option>
            </select>
          </div>
        </div>

        {/* Contract scorecard table */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden"}}>
          {/* Column headers */}
          <div style={{
            display:"grid",
            gridTemplateColumns:"1.4fr 80px 80px 2fr 1fr 90px 90px 120px 20px",
            gap:8, padding:"9px 14px",
            background: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
            borderBottom:`1px solid ${C.cardBord}`,
            fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase",
            fontFamily:FONT,
          }}>
            <div>Supplier · Terminal</div>
            <div>Status</div>
            <div style={{textAlign:"right"}}>Tier</div>
            <div>MTD · Commit · Projected</div>
            <div style={{textAlign:"right"}}>Need/day</div>
            <div style={{textAlign:"right"}}>Penalty risk</div>
            <div style={{textAlign:"right"}}>Renewal</div>
            <div style={{textAlign:"center"}}>Action</div>
          </div>
          {filtered.length === 0 ? (
            <div style={{padding:"30px", textAlign:"center", color:C.textMut, fontSize:11, fontFamily:FONT}}>
              No contracts match this filter.
            </div>
          ) : filtered.map((r, ri) => {
            const progressColor = r.isAtRisk ? "#DC2626" : r.isOverlifting ? "#F59E0B" : "#16A34A";
            const projectedPct = r.projectedPct;
            const isExpanded = expandedContract === r.supplier.id;
            const history = isExpanded ? generateContractHistory(r.supplier, r.commit) : null;
            return (
              <React.Fragment key={r.supplier.id}>
              <div
                onClick={()=>setExpandedContract(isExpanded ? null : r.supplier.id)}
                style={{
                display:"grid",
                gridTemplateColumns:"1.4fr 80px 80px 2fr 1fr 90px 90px 120px 20px",
                gap:8, padding:"12px 14px", alignItems:"center",
                borderBottom: ri < filtered.length-1 && !isExpanded ? `1px solid ${C.cardBord}` : "none",
                fontFamily:FONT,
                cursor:"pointer",
                background: isExpanded ? (darkMode?"rgba(200,164,74,.04)":"#F8FAFB") : "transparent",
                transition:"background .12s",
              }}
              onMouseEnter={e=>{ if (!isExpanded) e.currentTarget.style.background = darkMode?"rgba(255,255,255,.02)":"#FAFBFD"; }}
              onMouseLeave={e=>{ e.currentTarget.style.background = isExpanded ? (darkMode?"rgba(200,164,74,.04)":"#F8FAFB") : "transparent"; }}
              >
                {/* Supplier + terminal */}
                <div style={{minWidth:0, display:"flex", alignItems:"center", gap:20, paddingLeft:8}}>
                  <SupplierLogo supplierName={r.supplier.name} supplierShort={r.supplier.short} size={32}/>
                  <div style={{minWidth:0}}>
                    <div style={{fontSize:11.5, fontWeight:700, color:C.textPri}}>
                      {r.supplier.name}
                    </div>
                    <div style={{fontSize:10, color:C.textSec, marginTop:1}}>
                      <span style={{display:"inline-flex",alignItems:"center",gap:4}}><ZoneBadge terminalId={r.terminal.id}/>{r.terminal.name}</span>
                    </div>
                  </div>
                </div>
                {/* Status */}
                <div>
                  <span style={{
                    fontSize:9, fontWeight:800, padding:"2px 7px", borderRadius:10,
                    background: statusPillBg(r), color: statusPillColor(r),
                    letterSpacing:.4, textTransform:"uppercase",
                    border:`1px solid ${statusPillColor(r)}40`,
                  }}>
                    {statusPillText(r)}
                  </span>
                </div>
                {/* Tier */}
                <div style={{textAlign:"right"}}>
                  <span style={{
                    fontSize:9, fontWeight:800, padding:"2px 7px", borderRadius:3,
                    background: r.supplier.contractStatus==="primary" ? (darkMode?"rgba(22,163,74,.12)":"#F0FDF4") : (darkMode?"rgba(200,164,74,.12)":"#F8FAFB"),
                    color: r.supplier.contractStatus==="primary" ? "#16A34A" : "#F4D398",
                    letterSpacing:.4, textTransform:"uppercase",
                  }}>
                    {r.supplier.contractStatus === "primary" ? "PRI" : "SEC"}
                  </span>
                </div>
                {/* MTD + commit + progress + projected */}
                <div style={{minWidth:0}}>
                  <div style={{display:"flex", alignItems:"baseline", gap:6, flexWrap:"wrap"}}>
                    <span style={{fontSize:11, fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                      {(r.lifted/1_000_000).toFixed(2)}M
                    </span>
                    <span style={{fontSize:9.5, color:C.textMut}}>of</span>
                    <span style={{fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif"}}>
                      {(r.commit/1_000_000).toFixed(2)}M
                    </span>
                    <span style={{fontSize:9.5, color:C.textMut}}>→</span>
                    <span style={{fontSize:10.5, fontWeight:700, color:progressColor, fontFamily:"Arial,sans-serif"}}>
                      proj {(r.projectedEOM/1_000_000).toFixed(2)}M
                    </span>
                    {r.projectedShortfall > 0 && (
                      <span style={{fontSize:9.5, fontWeight:700, color:"#DC2626"}}>
                        (−{(r.projectedShortfall/1000).toFixed(0)}K)
                      </span>
                    )}
                    {r.projectedOverage > 0 && (
                      <span style={{fontSize:9.5, fontWeight:700, color:"#F59E0B"}}>
                        (+{(r.projectedOverage/1000).toFixed(0)}K)
                      </span>
                    )}
                  </div>
                  {/* Progress bar — shows actual MTD pace and projected position */}
                  <div style={{position:"relative", marginTop:6, height:8, background:darkMode?"rgba(255,255,255,.04)":"#F0F3F8", borderRadius:4, overflow:"hidden"}}>
                    {/* MTD bar (solid) */}
                    <div style={{
                      position:"absolute", left:0, top:0, bottom:0,
                      width:`${Math.min(100, r.pctLifted*100)}%`,
                      background: progressColor,
                      borderRadius:"4px 0 0 4px",
                    }}/>
                    {/* Projected extension (striped/lighter) */}
                    {projectedPct > r.pctLifted && (
                      <div style={{
                        position:"absolute",
                        left:`${r.pctLifted*100}%`,
                        top:0, bottom:0,
                        width:`${Math.min(100-r.pctLifted*100, (projectedPct - r.pctLifted)*100)}%`,
                        background: `repeating-linear-gradient(45deg, ${progressColor}55, ${progressColor}55 4px, ${progressColor}22 4px, ${progressColor}22 8px)`,
                      }}/>
                    )}
                    {/* 100% target marker */}
                    <div style={{
                      position:"absolute", left:"100%", top:-2, bottom:-2, width:2,
                      background: C.textMut, transform:"translateX(-1px)",
                    }}/>
                  </div>
                  <div style={{fontSize:9, color:C.textMut, marginTop:3, fontFamily:"Arial,sans-serif"}}>
                    {Math.round(r.pctLifted*100)}% lifted · pace {(r.dailyPace/1000).toFixed(0)}K/day
                  </div>
                </div>
                {/* Need per day */}
                <div style={{textAlign:"right"}}>
                  {r.neededPerDay > 0 ? (
                    <>
                      <div style={{fontSize:11.5, fontWeight:700, color: r.isAtRisk ? "#DC2626" : C.textPri, fontFamily:"Arial,sans-serif"}}>
                        {(r.neededPerDay/1000).toFixed(0)}K
                      </div>
                      <div style={{fontSize:9, color:C.textMut, marginTop:1}}>gal/day</div>
                    </>
                  ) : (
                    <span style={{fontSize:10.5, color:C.textMut, fontStyle:"italic"}}>—</span>
                  )}
                </div>
                {/* Penalty exposure */}
                <div style={{textAlign:"right"}}>
                  {r.penaltyExposure > 0 ? (
                    <div style={{fontSize:11, fontWeight:700, color:"#DC2626", fontFamily:"Arial,sans-serif"}}>
                      ${Math.round(r.penaltyExposure).toLocaleString()}
                    </div>
                  ) : (
                    <span style={{fontSize:10.5, color:"#16A34A", fontWeight:700}}>$0</span>
                  )}
                </div>
                {/* Renewal */}
                <div style={{textAlign:"right"}}>
                  {r.daysToExpiry !== null ? (
                    <div style={{
                      fontSize:10.5, fontWeight: r.isRenewingSoon ? 700 : 500,
                      color: r.isRenewingSoon ? C.gold : C.textSec,
                      fontFamily:"Arial,sans-serif",
                    }}>
                      {r.daysToExpiry < 0 ? "Expired"
                       : r.daysToExpiry === 0 ? "Today"
                       : r.daysToExpiry <= 90 ? `${r.daysToExpiry}d`
                       : r.daysToExpiry <= 365 ? `${Math.round(r.daysToExpiry/30)}mo`
                       : `${(r.daysToExpiry/365).toFixed(1)}yr`}
                    </div>
                  ) : (
                    <span style={{fontSize:10.5, color:C.textMut}}>—</span>
                  )}
                </div>
                {/* Action */}
                <div style={{textAlign:"center"}}>
                  {r.isAtRisk ? (
                    <button
                      onClick={e=>{
                        e.stopPropagation();
                        // Set the Plan filter so the user only sees loads routable
                        // to this supplier-at-terminal. Cleared automatically when
                        // they navigate away from Plan.
                        setPlanFilter({
                          terminalId: r.terminal.id,
                          supplierShort: r.supplier.short,
                          reason: "bump-lifts",
                          message: `Bumping lifts for ${r.supplier.name} (${r.supplier.short}) at ${r.terminal.name} — ${Math.round((1 - r.projectedPct) * 100)}% under commit`,
                        });
                        setActiveTab("plan");
                        addToast(`Filtered to ${r.terminal.short} loads — route volume to ${r.supplier.short}`, "info");
                      }}
                      style={{
                        padding:"5px 10px", borderRadius:5, border:"none",
                        background:"#DC2626", color:"#fff",
                        fontSize:10, fontWeight:700, cursor:"pointer", fontFamily:FONT,
                      }}>
                      Bump lifts →
                    </button>
                  ) : r.isRenewingSoon ? (
                    <span style={{
                      fontSize:9.5, fontWeight:700, color:C.gold,
                      padding:"4px 8px", borderRadius:5,
                      background: darkMode?"rgba(200,164,74,.10)":"#FFF9E6",
                      border:`1px solid ${C.gold}40`,
                    }}>
                      Review renewal
                    </span>
                  ) : (
                    <span style={{fontSize:10, color:C.textMut, fontStyle:"italic"}}>—</span>
                  )}
                </div>
                {/* Chevron */}
                <div style={{textAlign:"center", fontSize:13, color:C.textMut, userSelect:"none"}}>
                  {isExpanded ? "▾" : "▸"}
                </div>
              </div>

              {/* EXPANSION PANEL — 6-month contract history drill-down */}
              {isExpanded && history && (
                <div style={{
                  padding:"14px 18px 18px 62px",
                  background: darkMode?"rgba(200,164,74,.03)":"#F8FAFB",
                  borderLeft:`3px solid ${C.gold}`,
                  borderBottom: ri < filtered.length-1 ? `1px solid ${C.cardBord}` : "none",
                  fontFamily:FONT,
                }}>
                  {/* Header + YTD roll-up */}
                  <div style={{display:"flex", justifyContent:"space-between", alignItems:"flex-end", marginBottom:12, flexWrap:"wrap", gap:10}}>
                    <div>
                      <div style={{fontSize:10.5, fontWeight:800, color:C.textSec, letterSpacing:.5, textTransform:"uppercase"}}>
                        6-Month Lift History
                      </div>
                      <div style={{fontSize:10, color:C.textMut, marginTop:2}}>
                        {r.supplier.name} at {r.terminal.name} — monthly commit vs lifted through Mar 26
                      </div>
                    </div>
                    {/* Roll-up stat tiles */}
                    <div style={{display:"flex", gap:8}}>
                      <div style={{
                        padding:"6px 12px", borderRadius:6,
                        background: darkMode?"rgba(255,255,255,.03)":"#fff",
                        border:`1px solid ${C.cardBord}`,
                      }}>
                        <div style={{fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.4}}>CUMULATIVE COMMIT</div>
                        <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:"Arial,sans-serif", marginTop:2}}>
                          {(history.cumulativeCommit/1_000_000).toFixed(2)}M<span style={{fontSize:9, color:C.textMut, fontWeight:500, marginLeft:3}}>gal</span>
                        </div>
                      </div>
                      <div style={{
                        padding:"6px 12px", borderRadius:6,
                        background: darkMode?"rgba(255,255,255,.03)":"#fff",
                        border:`1px solid ${C.cardBord}`,
                      }}>
                        <div style={{fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.4}}>CUMULATIVE LIFTED</div>
                        <div style={{fontSize:12, fontWeight:800,
                          color: history.cumulativePct < 0.98 ? "#DC2626" : history.cumulativePct > 1.05 ? "#F59E0B" : "#16A34A",
                          fontFamily:"Arial,sans-serif", marginTop:2}}>
                          {(history.cumulativeLifted/1_000_000).toFixed(2)}M
                          <span style={{fontSize:9, fontWeight:600, marginLeft:4}}>
                            ({(history.cumulativePct*100).toFixed(0)}%)
                          </span>
                        </div>
                      </div>
                      <div style={{
                        padding:"6px 12px", borderRadius:6,
                        background: history.totalPenalties > 0 ? (darkMode?"rgba(220,38,38,.08)":"#FEF7F7") : (darkMode?"rgba(255,255,255,.03)":"#fff"),
                        border:`1px solid ${history.totalPenalties > 0 ? "rgba(220,38,38,.3)" : C.cardBord}`,
                      }}>
                        <div style={{fontSize:8.5, fontWeight:800, color: history.totalPenalties > 0 ? "#DC2626" : C.textMut, letterSpacing:.4}}>PENALTIES PAID</div>
                        <div style={{fontSize:12, fontWeight:800,
                          color: history.totalPenalties > 0 ? "#DC2626" : C.textPri,
                          fontFamily:"Arial,sans-serif", marginTop:2}}>
                          ${history.totalPenalties.toLocaleString()}
                        </div>
                      </div>
                    </div>
                  </div>

                  {/* 6-month table — clean financial view */}
                  <div style={{marginBottom:10}}>
                    {/* Table header */}
                    <div style={{display:"grid", gridTemplateColumns:"70px 1fr 1fr 60px 70px", gap:8, fontSize:8.5, fontWeight:800, color:C.textMut, letterSpacing:.4, padding:"5px 8px", borderRadius:"5px 5px 0 0", background: darkMode?"rgba(255,255,255,.03)":"#F4F6F9"}}>
                      <div>MONTH</div>
                      <div style={{textAlign:"right"}}>COMMIT</div>
                      <div style={{textAlign:"right"}}>LIFTED</div>
                      <div style={{textAlign:"right"}}>% LIFT</div>
                      <div style={{textAlign:"right"}}>PENALTY</div>
                    </div>
                    {history.months.map((m, mi) => {
                      const pct = m.pctLifted;
                      const col = pct < 0.98 ? "#DC2626" : pct > 1.05 ? "#F59E0B" : "#16A34A";
                      const variance = m.lifted - m.commit;
                      return (
                        <div key={mi} style={{
                          display:"grid", gridTemplateColumns:"70px 1fr 1fr 60px 70px",
                          gap:8, padding:"7px 8px", alignItems:"center",
                          borderBottom:`1px solid ${C.cardBord}40`,
                          background: mi % 2 === 0 ? "transparent" : darkMode?"rgba(255,255,255,.01)":"rgba(0,0,0,.012)",
                        }}>
                          <div style={{fontSize:10.5, fontWeight:600, color:C.textSec, fontFamily:"Arial,sans-serif"}}>{m.month}</div>
                          <div style={{textAlign:"right", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif"}}>
                            {(m.commit/1_000_000).toFixed(2)}M
                          </div>
                          <div style={{textAlign:"right", fontFamily:"Arial,sans-serif"}}>
                            <span style={{fontSize:10.5, fontWeight:600, color:C.textPri}}>{(m.lifted/1_000_000).toFixed(2)}M</span>
                            <span style={{fontSize:9, marginLeft:4, color: variance >= 0 ? "#16A34A" : "#DC2626", fontWeight:600}}>
                              {variance >= 0 ? "+" : ""}{(variance/1000).toFixed(0)}K
                            </span>
                          </div>
                          <div style={{textAlign:"right"}}>
                            <span style={{
                              fontSize:10, fontWeight:800, color:"#fff",
                              background:col, padding:"1px 6px", borderRadius:4,
                              fontFamily:"Arial,sans-serif",
                            }}>
                              {(pct*100).toFixed(0)}%
                            </span>
                          </div>
                          <div style={{textAlign:"right", fontSize:10.5, color: m.penalty > 0 ? "#DC2626" : C.textMut, fontFamily:"Arial,sans-serif", fontWeight: m.penalty > 0 ? 700 : 400}}>
                            {m.penalty > 0 ? `$${m.penalty.toLocaleString()}` : "—"}
                          </div>
                        </div>
                      );
                    })}
                  </div>

                  {/* Two-column bottom section: peer comparison + forward projection */}
                  <div style={{display:"flex", gap:10, marginTop:10}}>

                    {/* PEER COMPARISON — other contracts at the same terminal */}
                    {(() => {
                      const peers = contractRows.filter(p =>
                        p.terminal.id === r.terminal.id && p.supplier.id !== r.supplier.id
                      );
                      if (peers.length === 0) return null;
                      return (
                        <div style={{flex:1, padding:"10px 12px", borderRadius:6,
                          background: darkMode?"rgba(255,255,255,.02)":"#F8FAFB",
                          border:`1px solid ${C.cardBord}`}}>
                          <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:8}}>
                            Other Suppliers at <ZoneBadge terminalId={r.terminal.id} size="sm"/> {r.terminal.short}
                          </div>
                          {peers.map((p, pi) => {
                            const pCol = p.projectedPct < 0.98 ? "#DC2626" : p.projectedPct > 1.05 ? "#F59E0B" : "#16A34A";
                            const diff = p.projectedPct - r.projectedPct;
                            return (
                              <div key={pi} style={{
                                display:"flex", alignItems:"center", justifyContent:"space-between",
                                padding:"5px 0",
                                borderBottom: pi < peers.length-1 ? `1px solid ${C.cardBord}40` : "none",
                                gap:8,
                              }}>
                                <div style={{display:"flex", alignItems:"center", gap:6, minWidth:0}}>
                                  <SupplierLogo supplierName={p.supplier.name} supplierShort={p.supplier.short} size={14}/>
                                  <span style={{fontSize:10.5, fontWeight:600, color:C.textPri, fontFamily:"Arial,sans-serif"}}>
                                    {p.supplier.short}
                                  </span>
                                  <span style={{fontSize:9, color:C.textMut}}>
                                    {p.supplier.contractStatus}
                                  </span>
                                </div>
                                <div style={{display:"flex", alignItems:"center", gap:6, flexShrink:0}}>
                                  <span style={{
                                    fontSize:10, fontWeight:800, color:"#fff",
                                    background:pCol, padding:"1px 6px", borderRadius:4,
                                    fontFamily:"Arial,sans-serif",
                                  }}>
                                    {(p.projectedPct*100).toFixed(0)}%
                                  </span>
                                  {Math.abs(diff) > 0.01 && (
                                    <span style={{fontSize:9, fontWeight:700,
                                      color: diff > 0 ? "#16A34A" : "#DC2626",
                                      fontFamily:"Arial,sans-serif",
                                    }}>
                                      {diff > 0 ? "+" : ""}{(diff*100).toFixed(0)}pp
                                    </span>
                                  )}
                                </div>
                              </div>
                            );
                          })}
                        </div>
                      );
                    })()}

                    {/* FORWARD PROJECTION — EOM outcome at current pace */}
                    {(() => {
                      const projGals = r.projectedEOM;
                      const projPct = r.projectedPct;
                      const shortfall = r.projectedShortfall;
                      const overage = r.projectedOverage;
                      const penalty = shortfall * (r.supplier.contractStatus === "primary" ? PENALTY_PRIMARY_PER_GAL : PENALTY_SECONDARY_PER_GAL);
                      const projCol = projPct < 0.98 ? "#DC2626" : projPct > 1.05 ? "#F59E0B" : "#16A34A";
                      // What pace is needed to hit 100% by EOM
                      const neededDaily = DAYS_REMAINING > 0 ? Math.max(0, r.commit - r.lifted) / DAYS_REMAINING : 0;
                      const currentDaily = r.dailyPace;
                      const paceGap = neededDaily - currentDaily;
                      return (
                        <div style={{flex:1, padding:"10px 12px", borderRadius:6,
                          background: darkMode?"rgba(255,255,255,.02)":"#F8FAFB",
                          border:`1px solid ${C.cardBord}`}}>
                          <div style={{fontSize:9, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:8}}>
                            EOM Projection · Day {DAYS_ELAPSED}/{DAYS_IN_MONTH}
                          </div>
                          {/* Projected fill bar */}
                          <div style={{position:"relative", height:6, borderRadius:3,
                            background: darkMode?"rgba(255,255,255,.06)":"#E8ECF0", marginBottom:10}}>
                            <div style={{
                              position:"absolute", left:0, top:0, bottom:0,
                              width:`${Math.min(100, projPct*100)}%`,
                              background:projCol, borderRadius:3,
                            }}/>
                            {/* Today marker */}
                            <div style={{
                              position:"absolute", top:-3, bottom:-3,
                              left:`${(DAYS_ELAPSED/DAYS_IN_MONTH)*100}%`,
                              width:2, background: C.gold, borderRadius:1,
                            }}/>
                          </div>
                          <div style={{display:"grid", gridTemplateColumns:"1fr 1fr", gap:8}}>
                            <div>
                              <div style={{fontSize:8.5, color:C.textMut, fontWeight:700, letterSpacing:.3}}>PROJECTED EOM</div>
                              <div style={{fontSize:13, fontWeight:800, color:projCol, fontFamily:"Arial,sans-serif", marginTop:2}}>
                                {(projGals/1_000_000).toFixed(2)}M
                                <span style={{fontSize:10, fontWeight:600, marginLeft:4}}>({(projPct*100).toFixed(0)}%)</span>
                              </div>
                            </div>
                            <div>
                              <div style={{fontSize:8.5, color:C.textMut, fontWeight:700, letterSpacing:.3}}>
                                {shortfall > 0 ? "PENALTY EXPOSURE" : "OVERAGE"}
                              </div>
                              <div style={{fontSize:13, fontWeight:800, fontFamily:"Arial,sans-serif", marginTop:2,
                                color: shortfall > 0 ? "#DC2626" : "#F59E0B"}}>
                                {shortfall > 0 ? `$${Math.round(penalty).toLocaleString()}` : `+${(overage/1000).toFixed(0)}K gal`}
                              </div>
                            </div>
                            <div>
                              <div style={{fontSize:8.5, color:C.textMut, fontWeight:700, letterSpacing:.3}}>CURRENT PACE</div>
                              <div style={{fontSize:11, fontWeight:700, color:C.textSec, fontFamily:"Arial,sans-serif", marginTop:2}}>
                                {(currentDaily/1000).toFixed(1)}K gal/day
                              </div>
                            </div>
                            <div>
                              <div style={{fontSize:8.5, color:C.textMut, fontWeight:700, letterSpacing:.3}}>
                                {paceGap > 0 ? "NEED TO ADD" : "CAN EASE TO"}
                              </div>
                              <div style={{fontSize:11, fontWeight:700, fontFamily:"Arial,sans-serif", marginTop:2,
                                color: paceGap > 0 ? "#DC2626" : "#16A34A"}}>
                                {paceGap > 0 ? `+${(paceGap/1000).toFixed(1)}K` : `${(Math.abs(paceGap)/1000).toFixed(1)}K`} gal/day
                              </div>
                            </div>
                          </div>
                        </div>
                      );
                    })()}

                  </div>
                </div>
              )}
              </React.Fragment>
            );
          })}
        </div>

        {/* Methodology footer */}
        <div style={{
          padding:"10px 14px", borderRadius:8,
          background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
          border:`1px dashed ${C.cardBord}`,
          fontSize:10, color:C.textMut, lineHeight:1.5, fontFamily:FONT,
        }}>
          <strong style={{color:C.textSec}}>Methodology:</strong> Projected EOM position uses linear extrapolation from current pace (lifted MTD ÷ days elapsed × days in month). "At risk" threshold is projected shortfall &gt; 2% of commitment. Penalty exposure assumes ${PENALTY_PRIMARY_PER_GAL.toFixed(3)}/gal on primary contract shortfall and ${PENALTY_SECONDARY_PER_GAL.toFixed(3)}/gal on secondary — actual contract terms may differ. Spot-only suppliers excluded (no commitment). Uses supplier-at-terminal data from the Suppliers layer.
        </div>
      </div>
    );
  };

  //  Tab: Forecast 
  const renderForecast = () => {
    const FONT = "Arial,sans-serif";
    const fwd = FORWARD[forecastTerminal]?.[forecastGrade] || [];
    const hist = RACK_HISTORY[forecastTerminal]?.[forecastGrade] || [];
    const sig = SIGNALS[forecastTerminal]?.[forecastGrade];
    const t = TERMINALS.find(x=>x.id===forecastTerminal);
    const currentRack = RACK_PRICES[forecastTerminal]?.[forecastGrade]||0;

    // Buy today vs wait analysis
    const day3Price = fwd[2]?.val||currentRack;
    const day7Price = fwd[6]?.val||currentRack;
    const day3Delta = day3Price - currentRack;
    const day7Delta = day7Price - currentRack;
    const buyNowSaves50k = -day7Delta * 50000;

    return (
      <div style={{display:"flex",flexDirection:"column",gap:14}}>
        {/* Selectors */}
        <div style={{display:"flex",gap:8,alignItems:"center",flexWrap:"wrap"}}>
          {TERMINALS.map(tm=>(
            <button key={tm.id} onClick={()=>setForecastTerminal(tm.id)}
              style={{padding:"7px 14px",borderRadius:7,border:`1.5px solid ${forecastTerminal===tm.id?C.gold:C.cardBord}`,background:forecastTerminal===tm.id?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent",color:forecastTerminal===tm.id?C.gold:C.textSec,fontSize:12,fontWeight:forecastTerminal===tm.id?700:400,cursor:"pointer",fontFamily:FONT}}>
              {tm.short}
            </button>
          ))}
          <div style={{width:1,height:22,background:C.cardBord,margin:"0 4px"}}/>
          {GRADES.map(g=>(
            <button key={g} onClick={()=>setForecastGrade(g)}
              style={{padding:"7px 14px",borderRadius:7,border:`1.5px solid ${forecastGrade===g?C.blue:C.cardBord}`,background:forecastGrade===g?(darkMode?"rgba(59,130,246,.12)":"#EFF6FF"):"transparent",color:forecastGrade===g?C.blue:C.textSec,fontSize:12,fontWeight:forecastGrade===g?700:400,cursor:"pointer",fontFamily:FONT}}>
              {g}
            </button>
          ))}
        </div>

        {/* Buy timing decision */}
        <div style={{display:"flex",gap:14}}>
          {/* Main decision card */}
          <div style={{flex:"0 0 320px",background:C.cardBg,border:`2px solid ${sig?.color||C.cardBord}`,borderRadius:10,padding:18}}>
            <div style={{fontSize:10,fontWeight:700,color:C.textMut,textTransform:"uppercase",letterSpacing:.8,fontFamily:FONT,marginBottom:8}}>BUY TIMING DECISION</div>
            {sig&&<SignalBadge signal={sig.signal} color={sig.color} size="lg"/>}
            <div style={{fontSize:16,fontWeight:800,color:C.textPri,fontFamily:FONT,marginTop:12,lineHeight:1.3}}>{sig?.reason}</div>
            <div style={{fontSize:12,color:C.textSec,marginTop:8,lineHeight:1.5}}>{sig?.savingsNote}</div>
            <div style={{marginTop:16,display:"flex",flexDirection:"column",gap:8}}>
              {[
                {label:"Today's rack",    val:`$${currentRack.toFixed(4)}`, color:C.textPri},
                {label:"Forecast: Day 3", val:`$${day3Price.toFixed(4)}`, color:day3Delta>0?C.red:C.green, delta:day3Delta},
                {label:"Forecast: Day 7", val:`$${day7Price.toFixed(4)}`, color:day7Delta>0?C.red:C.green, delta:day7Delta},
              ].map((row,i)=>(
                <div key={i} style={{display:"flex",justifyContent:"space-between",padding:"7px 10px",borderRadius:6,background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                  <span style={{fontSize:11,color:C.textSec,fontFamily:FONT}}>{row.label}</span>
                  <div style={{textAlign:"right"}}>
                    <span style={{fontSize:12,fontWeight:800,color:row.color,fontFamily:FONT}}>{row.val}</span>
                    {row.delta!==undefined&&<span style={{fontSize:10,color:row.color,marginLeft:6}}>{row.delta>0?"":""}${Math.abs(row.delta).toFixed(4)}</span>}
                  </div>
                </div>
              ))}
            </div>
            {/* 50K gal impact */}
            <div style={{marginTop:14,padding:"12px 14px",borderRadius:8,background:buyNowSaves50k>0?(darkMode?"rgba(34,197,94,.12)":"#F0FDF4"):(darkMode?"rgba(239,68,68,.1)":"#FEF2F2"),border:`1px solid ${buyNowSaves50k>0?C.green:C.red}40`,textAlign:"center"}}>
              <div style={{fontSize:10,color:C.textSec,fontFamily:FONT}}>On 50,000 gal — buying today vs Day 7</div>
              <div style={{fontSize:22,fontWeight:900,color:buyNowSaves50k>0?C.green:C.red,fontFamily:FONT}}>
                {buyNowSaves50k>0?"SAVES ":"COSTS "}${Math.abs(buyNowSaves50k).toFixed(0).replace(/\B(?=(\d{3})+(?!\d))/g,",")}
              </div>
            </div>
          </div>

          {/* Forecast chart */}
          <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
            <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}>{t?.name} · {forecastGrade} — 14-Day Rack Price Forecast</div>
            <div style={{fontSize:10.5,color:C.textSec,marginBottom:12}}>Center line = model prediction · Shaded band = 95% confidence interval · Dashed = today</div>
            <ForecastBand pts={fwd} color={C.blue} h={140} C={C} darkMode={darkMode}/>
            {/* 30d history + forecast combined */}
            <div style={{marginTop:12}}>
              <div style={{fontSize:10,color:C.textSec,fontFamily:FONT,marginBottom:4}}>30-Day Historical Context</div>
              <Spark data={hist} color={C.gold} h={44}/>
            </div>
          </div>
        </div>

        {/* Volume impact table */}
        <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
          <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}>Buy Now vs Wait — Dollar Impact at Various Volumes</div>
          <table style={{width:"100%",borderCollapse:"collapse"}}>
            <thead>
              <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                {["Volume (gal)","Buy Today","Wait 3 Days","Wait 7 Days","Δ vs Day 3","Δ vs Day 7","Recommendation"].map(h=>(
                  <th key={h} style={{padding:"8px 12px",fontSize:9.5,color:C.textMut,fontWeight:700,textAlign:h==="Volume (gal)"||h==="Recommendation"?"left":"right",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT}}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {[25000,50000,100000,150000,200000].map((vol,vi)=>{
                const todayCost = vol * currentRack;
                const day3Cost  = vol * day3Price;
                const day7Cost  = vol * day7Price;
                const d3 = day3Cost - todayCost;
                const d7 = day7Cost - todayCost;
                const rec = d7>200?"Buy Today":d7<-200?"Wait 7d":"On Plan";
                const recColor = rec==="Buy Today"?C.green:rec==="Wait 7d"?C.amber:C.textSec;
                return (
                  <tr key={vol} style={{borderBottom:`1px solid ${C.cardBord}`,background:vi%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)")}}>
                    <td style={{padding:"8px 12px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{(vol/1000).toFixed(0)}K</td>
                    <td style={{padding:"8px 12px",textAlign:"right",fontSize:11,color:C.textPri,fontFamily:FONT}}>${(todayCost/1000).toFixed(1)}K</td>
                    <td style={{padding:"8px 12px",textAlign:"right",fontSize:11,color:d3>0?C.red:C.green,fontFamily:FONT}}>${(day3Cost/1000).toFixed(1)}K</td>
                    <td style={{padding:"8px 12px",textAlign:"right",fontSize:11,color:d7>0?C.red:C.green,fontFamily:FONT}}>${(day7Cost/1000).toFixed(1)}K</td>
                    <td style={{padding:"8px 12px",textAlign:"right",fontSize:11,fontWeight:700,color:d3>0?C.red:C.green,fontFamily:FONT}}>{d3>0?"+":""} ${(d3/1000).toFixed(1)}K</td>
                    <td style={{padding:"8px 12px",textAlign:"right",fontSize:11,fontWeight:700,color:d7>0?C.red:C.green,fontFamily:FONT}}>{d7>0?"+":""} ${(d7/1000).toFixed(1)}K</td>
                    <td style={{padding:"8px 12px"}}>
                      <span style={{fontSize:10,fontWeight:700,padding:"2px 9px",borderRadius:8,background:`${recColor}18`,color:recColor,fontFamily:FONT}}>{rec}</span>
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      </div>
    );
  };

  //  Tab: Dispatch 
  const renderDispatch = () => {
    const FONT = "Arial,sans-serif";
    const totalTrucks     = CARRIER_FLEET.reduce((a,c)=>a+c.trucks,0);
    const availTrucks     = CARRIER_FLEET.reduce((a,c)=>a+c.available,0);
    const inTransit       = ACTIVE_LOADS.filter(l=>l.status==="EN ROUTE").length;
    const loading         = ACTIVE_LOADS.filter(l=>l.status==="LOADING").length;
    const delivering      = ACTIVE_LOADS.filter(l=>l.status==="DELIVERING").length;
    const detentionToday  = DETENTION_LOG.filter(d=>d.date==="Apr 16").reduce((a,d)=>a+d.cost,0);
    const hosWarning      = CARRIER_FLEET.flatMap(c=>c.tractors).filter(t=>t.hos<4 && t.status!=="MAINTENANCE" && t.status!=="HOS RESET");
    const maintenanceTrucks = CARRIER_FLEET.flatMap(c=>c.tractors).filter(t=>t.status==="MAINTENANCE");
    const pendingLoads    = DEPLETION.filter(d=>d.minReorder<=3).sort((a,b)=>a.minReorder-b.minReorder);

    const statusColor = s => s==="EN ROUTE"?"#0891B2":s==="LOADING"?"#4F46E5":s==="DELIVERING"?"#059669":s==="AVAILABLE"?"#64748B":s==="HOS RESET"?"#0D1B2A":s==="SCHEDULED"?"#EA580C":"#EF4444";
    const statusBg    = s => ({
      "EN ROUTE":   darkMode?"rgba(8,145,178,.14)":"#ECFEFF",
      "LOADING":    darkMode?"rgba(79,70,229,.14)":"#F0FDFA",
      "DELIVERING": darkMode?"rgba(5,150,105,.14)":"#ECFDF5",
      "AVAILABLE":  darkMode?"rgba(100,116,139,.10)":"#F8FAFC",
      "HOS RESET":  darkMode?"rgba(13,22,40,.40)":"#F1F5F9",
      "MAINTENANCE":darkMode?"rgba(239,68,68,.10)":"#FFF5F5",
      "SCHEDULED":  darkMode?"rgba(234,88,12,.14)":"#FFF7ED",
    }[s]||"transparent");

    const subTabs = [
      {id:"live",       label:"Live Dispatch Board", icon:""},
      {id:"day",        label:"Day Schedule",        icon:""},
      {id:"fleet",      label:"Fleet & Drivers",     icon:""},
      {id:"loads",      label:"Load Planning",        icon:""},
      {id:"terminal",   label:"Terminal Status",      icon:""},
      {id:"detention",  label:"Detention & O/S",      icon:""},
      {id:"compliance", label:"Compliance",           icon:""},
    ];

    return (
      <div style={{display:"flex",flexDirection:"column",gap:12}}>

        {/*  KPI Strip  */}
        <div style={{display:"flex",gap:8}}>
          {[
            {label:"Trucks Available", val:`${availTrucks}/${totalTrucks}`,    sub:`${Math.round(availTrucks/totalTrucks*100)}% idle capacity`,       color:availTrucks>8?C.green:C.amber},
            {label:"Loads In Transit", val:inTransit,                          sub:`${loading} loading · ${delivering} delivering`,                   color:C.blue},
            {label:"Loads Needed",     val:pendingLoads.length,                sub:`${pendingLoads.filter(d=>d.minCritical<=1).length} critical <24h`, color:pendingLoads.filter(d=>d.minCritical<=1).length>0?C.red:C.amber},
            {label:"HOS Warnings",     val:hosWarning.length,                  sub:`${maintenanceTrucks.length} trucks in maintenance`,                color:hosWarning.length>0?C.amber:C.green},
            {label:"Detention Today",  val:`$${detentionToday}`,               sub:`${DETENTION_LOG.filter(d=>d.date==="Apr 16").length} incidents`,   color:detentionToday>100?C.red:C.amber},
            {label:"Avg Rack Wait",    val:`${Math.round(Object.values(TERMINAL_STATUS).reduce((a,t)=>a+t.rackWait,0)/Object.keys(TERMINAL_STATUS).length)}min`, sub:"across all terminals", color:C.textPri},
          ].map((k,i)=><KpiCard key={i} {...k} C={C} darkMode={darkMode} glass={true}/>)}
        </div>

        {/*  Sub-nav  */}
        <div style={{display:"flex",gap:4,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:8,padding:4}}>
          {subTabs.map(t=>(
            <button key={t.id} onClick={()=>setDispatchTab(t.id)}
              style={{flex:1,padding:"7px 6px",borderRadius:6,border:"none",cursor:"pointer",fontFamily:FONT,fontSize:11,fontWeight:dispatchTab===t.id?700:400,
                background:dispatchTab===t.id?(darkMode?"rgba(200,164,74,.18)":"#FFF9E6"):"transparent",
                color:dispatchTab===t.id?C.gold:C.textSec,transition:"all .15s"}}>
              {t.icon} {t.label}
            </button>
          ))}
        </div>

        {/*  LIVE DISPATCH BOARD  */}
        {dispatchTab==="live" && (
          <div style={{display:"flex",gap:14,minHeight:600}}>

            {/*  LEFT: Timeline + queue  */}
            <div style={{flex:1,minWidth:0,display:"flex",flexDirection:"column",gap:12}}>

              {/* Timeline card */}
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden"}}>

                {/* Controls bar */}
                <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"10px 16px",borderBottom:`1px solid ${C.cardBord}`,flexWrap:"wrap",gap:8}}>
                  <div style={{display:"flex",alignItems:"center",gap:8}}>
                    <button onClick={()=>setWeekOffset(0)}
                      style={{padding:"5px 12px",borderRadius:6,border:`1px solid ${weekOffset===0?C.gold:C.cardBord}`,background:weekOffset===0?(darkMode?"rgba(200,164,74,.15)":"#FFF9E6"):"transparent",color:weekOffset===0?C.gold:C.textSec,fontSize:11,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                      Today
                    </button>
                    <div style={{display:"flex",gap:2}}>
                      <button onClick={()=>setWeekOffset(w=>w-1)}
                        style={{width:28,height:28,borderRadius:6,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:15,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}>‹</button>
                      <button onClick={()=>setWeekOffset(w=>w+1)}
                        style={{width:28,height:28,borderRadius:6,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:15,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}>›</button>
                    </div>
                    <span style={{fontSize:13,fontWeight:700,color:C.textPri,fontFamily:FONT}}>
                      {(() => { const d=getWeekDates(weekOffset); return `${["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"][new Date(2025,3,16+weekOffset*7).getMonth()]} ${d[0].num}–${d[6].num}, 2025`; })()}
                    </span>
                  </div>
                  <div style={{display:"flex",gap:6,alignItems:"center",flexWrap:"wrap"}}>
                    {/* Status filter pills */}
                    {["ALL","LOADING","EN ROUTE","DELIVERING","SCHEDULED"].map(s=>{
                      const col = s==="ALL"?C.textSec:s==="LOADING"?"#4F46E5":s==="EN ROUTE"?"#0891B2":s==="DELIVERING"?"#059669":"#EA580C";
                      const cnt = s==="ALL"?liveLoads.length:liveLoads.filter(l=>l.status===s).length;
                      return (
                        <button key={s} onClick={()=>setStatusFilter(s)}
                          style={{display:"flex",alignItems:"center",gap:5,padding:"4px 10px",borderRadius:20,border:`1.5px solid ${statusFilter===s?col:C.cardBord}`,background:statusFilter===s?`${col}18`:"transparent",cursor:"pointer",fontFamily:FONT}}>
                          {s!=="ALL"&&<div style={{width:7,height:7,borderRadius:"50%",background:col}}/>}
                          <span style={{fontSize:10,fontWeight:700,color:statusFilter===s?col:C.textSec}}>{s} {cnt>0&&cnt}</span>
                        </button>
                      );
                    })}
                    {/* Carrier filter */}
                    <select value={carrierFilter} onChange={e=>setCarrierFilter(e.target.value)}
                      style={{padding:"4px 8px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textSec,fontSize:10.5,cursor:"pointer",fontFamily:FONT}}>
                      <option value="ALL">All carriers</option>
                      {CARRIER_FLEET.map(c=><option key={c.id} value={c.short}>{c.short}</option>)}
                    </select>
                  </div>
                </div>

                {/* Timeline grid */}
                {(() => {
                  const DAYS = getWeekDates(weekOffset);
                  const COL_W = 118;
                  const LABEL_W = 158;
                  const barColor = s => s==="LOADING"?"#4F46E5":s==="EN ROUTE"?"#0891B2":s==="DELIVERING"?"#059669":s==="SCHEDULED"?"#EA580C":"transparent";
                  const barBg = s => ({
                    "LOADING":   darkMode?"rgba(79,70,229,.16)":"rgba(13,148,136,.10)",
                    "EN ROUTE":  darkMode?"rgba(8,145,178,.16)":"rgba(8,145,178,.10)",
                    "DELIVERING":darkMode?"rgba(5,150,105,.16)":"rgba(5,150,105,.10)",
                    "SCHEDULED": darkMode?"rgba(234,88,12,.14)":"rgba(234,88,12,.09)",
                  }[s]||"transparent");

                  // Build rows: one per tractor, find their load(s) in the displayed week
                  const weekStart = new Date(2025, 3, DAYS[0].num).getTime();
                  const weekEnd   = new Date(2025, 3, DAYS[6].num + 1).getTime();
                  let rows = CARRIER_FLEET.flatMap(c=>
                    c.tractors
                      .filter(t=>t.status!=="MAINTENANCE")
                      .map(t=>{
                        // Find the load assigned to this truck that falls in the visible week
                        const load = liveLoads.find(l=>{
                          if (l.truck!==t.unit||l.carrier!==c.short) return false;
                          if (!l.scheduledDate) return true; // legacy loads default to today
                          const ldMs = new Date(l.scheduledDate).getTime();
                          return ldMs >= weekStart && ldMs <= weekEnd;
                        });
                        return {carrier:c, tractor:t, load};
                      })
                  );
                  if(carrierFilter!=="ALL") rows=rows.filter(r=>r.carrier.short===carrierFilter);
                  if(statusFilter!=="ALL") rows=rows.filter(r=>r.load?.status===statusFilter||(statusFilter==="ALL"&&true));
                  rows = rows.slice(0,14);

                  return (
                    <div style={{overflowY:"auto",maxHeight:440}}>
                      {/* Day headers */}
                      <div style={{display:"flex",position:"sticky",top:0,background:C.cardBg,zIndex:3,borderBottom:`1px solid ${C.cardBord}`}}>
                        <div style={{width:LABEL_W,flexShrink:0,padding:"8px 14px",display:"flex",alignItems:"center",fontSize:9,color:C.textMut,fontWeight:700,textTransform:"uppercase",letterSpacing:.5,borderRight:`1px solid ${C.cardBord}`}}>DRIVER / TRUCK</div>
                        {DAYS.map((d,di)=>(
                          <div key={di} style={{flex:1,minWidth:COL_W,borderLeft:`1px solid ${C.cardBord}`,padding:"6px 0",textAlign:"center",background:d.isToday?(darkMode?"rgba(200,164,74,.08)":"#F8FAFB"):"transparent"}}>
                            <div style={{fontSize:9.5,fontWeight:700,color:d.isToday?C.gold:C.textMut,textTransform:"uppercase",letterSpacing:.6,fontFamily:FONT}}>{d.label}</div>
                            <div style={{fontSize:20,fontWeight:900,color:d.isToday?C.gold:C.textPri,fontFamily:FONT,lineHeight:1.1}}>{d.num}</div>
                          </div>
                        ))}
                      </div>

                      {/* Rows */}
                      {rows.map((row,ri)=>{
                        const ld = row.load;
                        const isSelected = selectedLoad?.id===ld?.id;
                        // Calculate which column this load belongs in based on its actual date
                        const dayIdx = ld ? (() => {
                          if (!ld.scheduledDate) return DAYS.findIndex(d=>d.isToday); // fallback: today col
                          // Parse just the day number from "2025-04-16" → 16
                          const ldDay = parseInt(ld.scheduledDate.split("-")[2], 10);
                          const di = DAYS.findIndex(d => d.num === ldDay);
                          return di >= 0 ? di : -1;
                        })() : -1;
                        const spanDays = ld ? (ld.spanDays||1) : 0;
                        
                        return (
                          <div key={`${row.carrier.id}-${row.tractor.id}`}
                            style={{display:"flex",alignItems:"stretch",borderBottom:`1px solid ${C.cardBord}`,minHeight:56,transition:"background .1s"}}>

                            {/* Driver label */}
                            <div style={{width:LABEL_W,flexShrink:0,padding:"8px 12px",display:"flex",alignItems:"center",gap:9,borderRight:`1px solid ${C.cardBord}`,background:darkMode?"rgba(255,255,255,.015)":"#FAFBFC"}}>
                              <div style={{width:30,height:30,borderRadius:"50%",background:"#F4D398",display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,fontWeight:800,color:"#0D1B2A",flexShrink:0,letterSpacing:-.5}}>
                                {row.tractor.driver.split(" ").map(n=>n[0]).join("")}
                              </div>
                              <div style={{minWidth:0}}>
                                <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{row.tractor.driver}</div>
                                <div style={{fontSize:9,color:C.textMut,fontFamily:FONT}}>{row.carrier.short} · {row.tractor.unit} · {row.tractor.hos}h HOS</div>
                              </div>
                            </div>

                            {/* Day cells */}
                            {DAYS.map((d,di)=>{
                              const hasLoad = ld && di>=dayIdx && di<dayIdx+spanDays;
                              const isStart = di===dayIdx;
                              const isAvail = !ld && row.tractor.status==="AVAILABLE" && d.isToday;
                              const isHosReset = row.tractor.status==="HOS RESET";
                              return (
                                <div key={di} style={{flex:1,minWidth:COL_W,borderLeft:`1px solid ${C.cardBord}`,position:"relative",padding:"5px 4px",display:"flex",alignItems:"center",background:d.isToday?(darkMode?"rgba(200,164,74,.03)":"rgba(200,164,74,.02)"):"transparent"}}>

                                  {isHosReset && d.isToday && (
                                    <div style={{width:"100%",padding:"5px 8px",borderRadius:6,background:darkMode?"rgba(139,92,246,.12)":"#F0FDFA",border:`1px dashed #8B5CF680`,display:"flex",alignItems:"center",gap:5}}>
                                      <span style={{fontSize:12}}></span>
                                      <span style={{fontSize:9.5,color:"#8B5CF6",fontWeight:700}}>HOS Reset</span>
                                    </div>
                                  )}

                                  {hasLoad && !isHosReset && (
                                    <div onClick={()=>setSelectedLoad(isSelected?null:ld)}
                                      style={{width:"100%",padding:"6px 9px",borderRadius:7,border:`1.5px solid ${isSelected?C.gold:barColor(ld.status)}${isSelected?"":"50"}`,background:isSelected?(darkMode?"rgba(200,164,74,.18)":"#FFF9E6"):barBg(ld.status),cursor:"pointer",transition:"all .14s",boxShadow:isSelected?`0 0 0 2px ${C.gold}40`:"none"}}>
                                      {isStart && (
                                        <>
                                          <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",gap:4,marginBottom:3}}>
                                            <span style={{fontSize:10,fontWeight:800,color:barColor(ld.status),fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{ld.id}</span>
                                            <span style={{fontSize:8,fontWeight:700,padding:"1px 5px",borderRadius:8,background:`${barColor(ld.status)}22`,color:barColor(ld.status),flexShrink:0,whiteSpace:"nowrap"}}>{ld.status}</span>
                                          </div>
                                          <div style={{fontSize:9.5,color:C.textSec,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap",marginBottom:4}}>{ld.dest}</div>
                                          <div style={{height:3,background:darkMode?"rgba(255,255,255,.1)":"rgba(0,0,0,.08)",borderRadius:2,overflow:"hidden"}}>
                                            <div style={{height:"100%",width:`${ld.pct}%`,background:barColor(ld.status),borderRadius:2,transition:"width .3s"}}/>
                                          </div>
                                        </>
                                      )}
                                      {!isStart && (
                                        <div style={{height:3,background:barColor(ld.status),borderRadius:2,opacity:.5}}/>
                                      )}
                                    </div>
                                  )}

                                  {isAvail && !hasLoad && (
                                    <button onClick={()=>{setDispatchTarget({storeId:DEPLETION[0]?.storeId,grade:"Regular",vol:8000,truckUnit:row.tractor.unit,carrierId:row.carrier.id});setDispatchCarrierId(row.carrier.id);setDispatchTruckId(row.tractor.id);setShowDispatchModal(true);}}
                                      style={{width:"100%",padding:"7px 6px",borderRadius:7,border:`1.5px dashed ${C.cardBord}`,background:"transparent",color:C.textMut,fontSize:9.5,cursor:"pointer",fontFamily:FONT,display:"flex",alignItems:"center",justifyContent:"center",gap:4,transition:"all .15s"}}
                                      onMouseEnter={e=>{e.currentTarget.style.borderColor=C.gold;e.currentTarget.style.color=C.gold;}}
                                      onMouseLeave={e=>{e.currentTarget.style.borderColor=C.cardBord;e.currentTarget.style.color=C.textMut;}}>
                                      + Assign
                                    </button>
                                  )}
                                </div>
                              );
                            })}
                          </div>
                        );
                      })}

                      {rows.length===0 && (
                        <div style={{padding:"40px 0",textAlign:"center",color:C.textMut,fontSize:13}}>
                          No loads match the current filters
                        </div>
                      )}
                    </div>
                  );
                })()}
              </div>

              {/* Reorder queue */}
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:12}}>
                  <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT}}> Reorder Queue</div>
                  <span style={{fontSize:10,fontWeight:700,padding:"3px 9px",borderRadius:20,background:darkMode?"rgba(239,68,68,.12)":"#FFF5F5",color:C.red,border:`1px solid ${C.red}30`}}>{DEPLETION.filter(d=>d.minReorder<=3).length} stores</span>
                </div>
                <div style={{display:"flex",flexDirection:"column",gap:5}}>
                  {DEPLETION.filter(d=>d.minReorder<=3).sort((a,b)=>a.minReorder-b.minReorder).slice(0,8).map((d,di)=>{
                    const store = STORES.find(s=>s.id===d.storeId);
                    const urgGrade = GRADES.find(g=>d.forecast[g]?.daysToReorder<=3)||"Regular";
                    const vol = Math.round((store?.tanks?.[urgGrade]||10000)*0.78/500)*500;
                    const term = TERMINALS.find(t=>t.id===store?.terminal);
                    const avail = CARRIER_FLEET.find(c=>c.available>0&&c.terminalAccess.includes(store?.terminal||""));
                    const isCrit = d.minCritical<=1;
                    const alreadyDispatched = liveLoads.some(l=>l.dest===store?.name&&["SCHEDULED","LOADING","EN ROUTE"].includes(l.status));
                    return (
                      <div key={d.storeId} style={{display:"flex",alignItems:"center",gap:10,padding:"9px 13px",borderRadius:8,border:`1px solid ${isCrit?C.red+"50":C.cardBord}`,background:isCrit?(darkMode?"rgba(239,68,68,.06)":"#FFF8F8"):alreadyDispatched?(darkMode?"rgba(34,197,94,.05)":"#F0FFF4"):darkMode?"rgba(255,255,255,.02)":"#FAFAFA"}}>
                        <div style={{width:28,height:28,borderRadius:"50%",background:alreadyDispatched?C.green:isCrit?"#EF4444":C.amber,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,fontWeight:900,color:"#fff",flexShrink:0}}>
                          {alreadyDispatched?"":isCrit?"!":di+1}
                        </div>
                        <div style={{flex:1,minWidth:0}}>
                          <div style={{fontSize:11,fontWeight:700,color:alreadyDispatched?C.green:isCrit?C.red:C.textPri,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{store?.name}</div>
                          <div style={{fontSize:9.5,color:C.textMut}}>{d.state} · {term?.short} · {urgGrade} · {vol.toLocaleString()} gal</div>
                        </div>
                        <div style={{textAlign:"center",flexShrink:0}}>
                          <div style={{fontSize:13,fontWeight:800,color:isCrit?C.red:d.minReorder<=1?C.amber:C.green,fontFamily:FONT}}>{d.minReorder.toFixed(1)}d</div>
                          <div style={{fontSize:8.5,color:C.textMut}}>left</div>
                        </div>
                        {alreadyDispatched ? (
                          <span style={{fontSize:10,fontWeight:700,padding:"4px 10px",borderRadius:6,background:darkMode?"rgba(34,197,94,.12)":"#F0FDF4",color:C.green,border:`1px solid ${C.green}30`,whiteSpace:"nowrap"}}> Dispatched</span>
                        ) : (
                          <button onClick={()=>{setDispatchTarget({storeId:d.storeId,grade:urgGrade,vol,storeName:store?.name,terminal:store?.terminal});setDispatchCarrierId(avail?.id||null);setDispatchTruckId(null);setShowDispatchModal(true);}}
                            style={{padding:"5px 12px",borderRadius:6,border:`1px solid ${C.gold}`,background:darkMode?"rgba(200,164,74,.12)":"#FFF9E6",color:C.gold,fontSize:10,fontWeight:700,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap",flexShrink:0}}>
                            Dispatch 
                          </button>
                        )}
                      </div>
                    );
                  })}
                </div>
              </div>
            </div>

            {/*  RIGHT: Detail panel + terminal status  */}
            <div style={{width:340,flexShrink:0,display:"flex",flexDirection:"column",gap:12}}>

              {selectedLoad ? (
                <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden",flex:1,display:"flex",flexDirection:"column"}}>
                  {/* Header */}
                  <div style={{padding:"12px 16px",borderBottom:`1px solid ${C.cardBord}`,display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0}}>
                    <div>
                      <div style={{fontSize:12,fontWeight:800,color:C.textPri,fontFamily:FONT}}>{selectedLoad.carrier} · {selectedLoad.id}</div>
                      <div style={{fontSize:10,color:C.textSec,marginTop:1}}>{selectedLoad.driver} · {selectedLoad.truck}</div>
                    </div>
                    <div style={{display:"flex",alignItems:"center",gap:8}}>
                      <span style={{fontSize:10,fontWeight:700,padding:"4px 10px",borderRadius:20,background:statusBg(selectedLoad.status),color:statusColor(selectedLoad.status),border:`1px solid ${statusColor(selectedLoad.status)}40`}}>{selectedLoad.status}</span>
                      <button onClick={()=>setSelectedLoad(null)} style={{width:24,height:24,borderRadius:"50%",border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textMut,fontSize:13,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center"}}></button>
                    </div>
                  </div>

                  {/* Route map — real Google Maps when key configured, SVG fallback otherwise */}
                  {(() => {
                    const originTerm = TERMINALS.find(t=>selectedLoad.origin.includes(t.name.split(",")[0]));
                    const destStore = STORES.find(s=>s.name===selectedLoad.dest);
                    const destTerm  = TERMINALS.find(t=>t.id===destStore?.terminal)||originTerm;
                    // Build SVG fallback (preserves existing visual when no API key is set)
                    const W=340,H=200,pad=20;
                    const lats=[27.5,38], lngs=[-85,-77];
                    const toX = lng=>pad+(lng-lngs[0])/(lngs[1]-lngs[0])*(W-pad*2);
                    const toY = lat=>H-pad-(lat-lats[0])/(lats[1]-lats[0])*(H-pad*2);
                    const ox = originTerm?toX(originTerm.lng):toX(-80);
                    const oy = originTerm?toY(originTerm.lat):toY(33);
                    const dx = destStore?toX(destStore.lng):(destTerm?toX(destTerm.lng):toX(-79));
                    const dy = destStore?toY(destStore.lat):(destTerm?toY(destTerm.lat):toY(34));
                    const cx1=(ox*0.4+dx*0.6), cy1=(oy*0.8+dy*0.2+10);
                    const pct=selectedLoad.pct/100;
                    const curX=Math.round((1-pct)*(1-pct)*ox+2*(1-pct)*pct*cx1+pct*pct*dx);
                    const curY=Math.round((1-pct)*(1-pct)*oy+2*(1-pct)*pct*cy1+pct*pct*dy);
                    const fallbackSvg = (
                      <div style={{background:darkMode?"#0D1A2D":"#E8F0F7",position:"relative",height:200}}>
                        <svg width="100%" height={H} viewBox={`0 0 ${W} ${H}`} preserveAspectRatio="xMidYMid slice">
                          {[40,80,120,160].map(y=><line key={y} x1="0" y1={y} x2={W} y2={y} stroke={darkMode?"#1E2A3A":"#D0DCE8"} strokeWidth="0.5"/>)}
                          {[70,140,210,280].map(x=><line key={x} x1={x} y1="0" x2={x} y2={H} stroke={darkMode?"#1E2A3A":"#D0DCE8"} strokeWidth="0.5"/>)}
                          <path d={`M ${ox},${oy} Q ${cx1},${cy1} ${dx},${dy}`} fill="none" stroke="#3B82F6" strokeWidth="2.5" strokeLinecap="round"/>
                          {pct>0&&<path d={`M ${ox},${oy} Q ${cx1},${cy1} ${curX},${curY}`} fill="none" stroke="#22C55E" strokeWidth="2.5" strokeLinecap="round"/>}
                          <circle cx={ox} cy={oy} r="7" fill="#22C55E" stroke={darkMode?"#0D1A2D":"#fff"} strokeWidth="2"/>
                          <rect x={dx-6} y={dy-6} width="12" height="12" rx="3" fill="#3B82F6" stroke={darkMode?"#0D1A2D":"#fff"} strokeWidth="2"/>
                          {pct>0&&pct<1&&(
                            <>
                              <circle cx={curX} cy={curY} r="13" fill="#3B82F6" fillOpacity="0.18"/>
                              <circle cx={curX} cy={curY} r="7" fill="#3B82F6" stroke={darkMode?"#0D1A2D":"#fff"} strokeWidth="2.5"/>
                              <rect x={curX-38} y={curY-24} width="76" height="18" rx="9" fill={darkMode?"#0D1B2A":"#fff"} stroke={darkMode?"#1E2840":"#D0DCE8"} strokeWidth="1"/>
                              <text x={curX} y={curY-12} textAnchor="middle" fontSize="9" fill={darkMode?"#E8EDF6":"#0D1B2A"} fontFamily="Arial,sans-serif" fontWeight="700">ETA {selectedLoad.eta||"TBD"}</text>
                            </>
                          )}
                          {TERMINALS.map(t=>(
                            <circle key={t.id} cx={toX(t.lng)} cy={toY(t.lat)} r="3" fill={darkMode?"#2A3A52":"#B0C4D8"} opacity="0.7"/>
                          ))}
                        </svg>
                        <div style={{position:"absolute",top:8,left:10,fontSize:9,fontWeight:700,color:darkMode?"#3D5070":"#7B9BB8"}}>
                          {selectedLoad.pct}% complete
                        </div>
                      </div>
                    );
                    return (
                      <GoogleRouteMap
                        load={selectedLoad}
                        originTerm={originTerm}
                        destStore={destStore}
                        destTerm={destTerm}
                        darkMode={darkMode} C={C} FONT={FONT}
                        FallbackSvg={fallbackSvg}
                      />
                    );
                  })()}

                  {/* Scrollable body */}
                  <div style={{overflowY:"auto",flex:1,padding:"14px 16px",display:"flex",flexDirection:"column",gap:14}}>
                    {/* Route stops */}
                    <div>
                      <div style={{fontSize:11,fontWeight:800,color:C.textPri,fontFamily:FONT,marginBottom:10}}>Route</div>
                      <div style={{position:"relative",paddingLeft:16}}>
                        <div style={{position:"absolute",left:4,top:10,bottom:10,width:1,borderLeft:`2px dashed ${C.cardBord}`}}/>
                        {[
                          {label:selectedLoad.origin, sub:`Departed ${selectedLoad.departed||"—"}`, dot:"green", done:true},
                          ...(selectedLoad.pct>5&&selectedLoad.pct<90?[{label:`En route · ${selectedLoad.pct}% complete`, sub:`ETA ${selectedLoad.eta}`, dot:"blue", done:false}]:[]),
                          {label:selectedLoad.dest, sub:`ETA ${selectedLoad.eta||"—"}`, dot:selectedLoad.pct>=90?"green":"gray", done:selectedLoad.pct>=90},
                        ].map((stop,si)=>(
                          <div key={si} style={{display:"flex",gap:10,marginBottom:si<2?14:0,alignItems:"flex-start"}}>
                            <div style={{width:11,height:11,borderRadius:stop.dot==="blue"?2:"50%",background:stop.dot==="green"?C.green:stop.dot==="blue"?C.blue:C.cardBord,border:`2px solid ${darkMode?"#0D1B2A":"#fff"}`,boxShadow:`0 0 0 2px ${stop.dot==="green"?C.green:stop.dot==="blue"?C.blue:C.textMut}`,flexShrink:0,marginTop:2}}/>
                            <div>
                              <div style={{fontSize:11,fontWeight:700,color:stop.done?C.textPri:stop.dot==="blue"?C.blue:C.textSec,fontFamily:FONT}}>{stop.label}</div>
                              <div style={{fontSize:9.5,color:C.textMut,marginTop:1}}>{stop.sub}</div>
                            </div>
                          </div>
                        ))}
                      </div>
                    </div>

                    {/* Overview */}
                    <div style={{borderTop:`1px solid ${C.cardBord}`,paddingTop:12}}>
                      <div style={{fontSize:11,fontWeight:800,color:C.textPri,fontFamily:FONT,marginBottom:8}}>Overview</div>
                      <div style={{display:"flex",flexDirection:"column",gap:6}}>
                        {[
                          {l:"Driver",    v:selectedLoad.driver},
                          {l:"Grade",     v:selectedLoad.grade},
                          {l:"Gallons",   v:selectedLoad.gals.toLocaleString()},
                          {l:"BOL #",     v:selectedLoad.bol||"Pending"},
                          {l:"Temp °F",   v:selectedLoad.tempF||"—"},
                          {l:"API Grav.", v:selectedLoad.apiGravity||"—"},
                          {l:"Detention", v:selectedLoad.detained>0?`${selectedLoad.detained} min — $${Math.round(selectedLoad.detained/60*(CARRIER_FLEET.find(c=>c.short===selectedLoad.carrier)?.detentionRate||75))}`:"None"},
                        ].map((row,ri)=>(
                          <div key={ri} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"3px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                            <span style={{fontSize:9.5,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,fontFamily:FONT}}>{row.l}</span>
                            <span style={{fontSize:11,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{row.v}</span>
                          </div>
                        ))}
                      </div>
                    </div>

                    {/* Actions */}
                    <div style={{borderTop:`1px solid ${C.cardBord}`,paddingTop:12,display:"flex",flexDirection:"column",gap:7}}>
                      {[
                        {icon:"",label:"Send to Driver",   action:()=>addToast(`Load details sent to ${selectedLoad.driver} via SMS`)},
                        {icon:"",label:"View / Print BOL", action:()=>addToast(`BOL ${selectedLoad.bol||"pending"} opened`)},
                        {icon:"",label:"Call Driver",       action:()=>addToast(`Calling ${selectedLoad.driver}...`)},
                        {icon:"",label:"Update Status",    action:()=>{ setLiveLoads(ls=>ls.map(l=>l.id===selectedLoad.id?{...l,pct:Math.min(100,l.pct+15)}:l)); addToast(`${selectedLoad.id} progress updated`); }},
                        {icon:"",label:"Flag Exception",   action:()=>addToast(`Exception flagged on ${selectedLoad.id}`,"warn")},
                      ].map((btn,bi)=>(
                        <button key={bi} onClick={btn.action}
                          style={{width:"100%",padding:"9px 0",borderRadius:8,border:`1px solid ${bi===0?C.gold:C.cardBord}`,background:bi===0?(darkMode?"rgba(200,164,74,.15)":"#FFF9E6"):"transparent",color:bi===0?C.gold:C.textSec,fontSize:11,fontWeight:bi===0?700:500,cursor:"pointer",fontFamily:FONT,display:"flex",alignItems:"center",justifyContent:"center",gap:7,transition:"background .14s"}}
                          onMouseEnter={e=>{ if(bi>0) e.currentTarget.style.background=darkMode?"rgba(255,255,255,.04)":"#F8FAFC"; }}
                          onMouseLeave={e=>{ if(bi>0) e.currentTarget.style.background="transparent"; }}>
                          {btn.icon} {btn.label}
                        </button>
                      ))}
                    </div>
                  </div>
                </div>
              ) : (
                /* Notification feed */
                <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden",flex:1,display:"flex",flexDirection:"column"}}>
                  <div style={{padding:"12px 16px",borderBottom:`1px solid ${C.cardBord}`,display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0}}>
                    <div style={{fontSize:12,fontWeight:800,color:C.textPri,fontFamily:FONT}}>Inbox</div>
                    <div style={{display:"flex",gap:6,alignItems:"center"}}>
                      {inboxRead.length<liveLoads.length&&<span style={{fontSize:10,fontWeight:700,padding:"2px 8px",borderRadius:10,background:darkMode?"rgba(59,130,246,.15)":"#EFF6FF",color:C.blue}}>{liveLoads.length-inboxRead.length} new</span>}
                      <button onClick={()=>setInboxRead(liveLoads.map(l=>l.id))} style={{fontSize:10,color:C.textMut,background:"none",border:"none",cursor:"pointer"}}>Mark all read</button>
                    </div>
                  </div>
                  <div style={{flex:1,overflowY:"auto"}}>
                    {[
                      ...liveLoads.map(l=>({
                        id:l.id,
                        dot:l.status==="DELIVERING"?C.green:l.status==="EN ROUTE"?C.blue:l.status==="SCHEDULED"?"#8B5CF6":C.amber,
                        msg:l.status==="DELIVERING"?`${l.id} arrived at ${l.dest}`:l.status==="EN ROUTE"?`${l.id} picked up at ${l.origin}`:l.status==="SCHEDULED"?`${l.id} scheduled — ${l.driver}`:l.status==="LOADING"?`${l.id} loading at ${l.origin}`:`${l.id} update`,
                        sub:`${l.driver} · ${l.carrier}-${l.truck}`,
                        time:l.departed||"09:00",
                        load:l,
                        isNew:!inboxRead.includes(l.id),
                      })),
                      {id:"sys1",dot:C.amber,msg:"Colonial nomination deadline: tomorrow 14:00 CT",sub:"System alert",time:"08:00",load:null,isNew:!inboxRead.includes("sys1")},
                      {id:"sys2",dot:C.red,  msg:"Richmond terminal: 45 min rack wait (HIGH)",   sub:"Terminal alert",time:"07:45",load:null,isNew:!inboxRead.includes("sys2")},
                    ].map((item,ii)=>(
                      <div key={item.id}
                        onClick={()=>{ if(item.load)setSelectedLoad(item.load); setInboxRead(r=>[...new Set([...r,item.id])]); }}
                        style={{display:"flex",gap:12,padding:"11px 16px",borderBottom:`1px solid ${C.cardBord}`,cursor:item.load?"pointer":"default",background:item.isNew?(darkMode?"rgba(59,130,246,.04)":"rgba(59,130,246,.03)"):"transparent",transition:"background .12s"}}
                        onMouseEnter={e=>{ if(item.load)e.currentTarget.style.background=darkMode?"rgba(255,255,255,.04)":"#F8FAFC"; }}
                        onMouseLeave={e=>{ e.currentTarget.style.background=item.isNew?(darkMode?"rgba(59,130,246,.04)":"rgba(59,130,246,.03)"):"transparent"; }}>
                        <div style={{width:36,height:36,borderRadius:"50%",background:darkMode?"rgba(255,255,255,.06)":"#F1F5F9",display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0,border:`1.5px solid ${item.dot}40`,position:"relative"}}>
                          <div style={{width:10,height:10,borderRadius:"50%",background:item.dot}}/>
                          {item.isNew&&<div style={{position:"absolute",top:0,right:0,width:8,height:8,borderRadius:"50%",background:C.blue,border:"2px solid "+(darkMode?C.cardBg:"#fff")}}/>}
                        </div>
                        <div style={{flex:1,minWidth:0}}>
                          <div style={{fontSize:11,fontWeight:item.isNew?700:500,color:C.textPri,fontFamily:FONT,lineHeight:1.4,marginBottom:2}}>{item.msg}</div>
                          <div style={{fontSize:9.5,color:C.textMut}}>{item.sub}</div>
                        </div>
                        <div style={{fontSize:9.5,color:C.textMut,flexShrink:0,paddingTop:2}}>{item.time}</div>
                      </div>
                    ))}
                  </div>
                  <div style={{padding:12,borderTop:`1px solid ${C.cardBord}`,flexShrink:0}}>
                    <button style={{width:"100%",padding:"9px 0",borderRadius:8,border:"none",background:C.blue,color:"#fff",fontSize:12,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                      View all messages
                    </button>
                  </div>
                </div>
              )}

              {/* Terminal quick status */}
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:14,flexShrink:0}}>
                <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:10}}> Terminal Status</div>
                {TERMINALS.map(t=>{
                  const ts=TERMINAL_STATUS[t.id];
                  const cColor=ts.congestion==="LOW"?C.green:ts.congestion==="MODERATE"?C.amber:C.red;
                  return (
                    <div key={t.id} style={{display:"flex",alignItems:"center",gap:8,padding:"6px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                      <div style={{width:8,height:8,borderRadius:"50%",background:cColor,flexShrink:0}}/>
                      <span style={{display:"inline-flex",alignItems:"center",gap:5,fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT,flex:1}}><ZoneBadge terminalId={t.id}/>{t.short}</span>
                      <div style={{display:"flex",gap:3}}>
                        {Array.from({length:ts.lanesTotal}).map((_,li)=>(
                          <div key={li} style={{width:8,height:14,borderRadius:2,background:li<ts.lanesOpen?C.green:(darkMode?"rgba(239,68,68,.45)":"#FCA5A5")}}/>
                        ))}
                      </div>
                      <span style={{fontSize:11,fontWeight:800,color:ts.rackWait>30?C.red:ts.rackWait>15?C.amber:C.green,fontFamily:FONT,width:32,textAlign:"right"}}>{ts.rackWait}m</span>
                    </div>
                  );
                })}
              </div>
            </div>
          </div>
        )}

        {/* ─── DAY SCHEDULE — driver × hour Gantt ─────────────────────────── */}
        {/* Hourly timeline of every available driver for a chosen day. Each      */}
        {/* driver row shows their HOS bar, then the day's planned trips placed   */}
        {/* on a 5 AM – 9 PM time axis. Live loads (LOADING/EN ROUTE/DELIVERING)  */}
        {/* render in their actual status colors; trips planned by the optimizer  */}
        {/* but not yet assigned render as ghost blocks the dispatcher can claim. */}
        {dispatchTab==="day" && (() => {
          // ── Time axis configuration ─────────────────────────────────────
          const DAY_START_HR = 5;      // 5 AM
          const DAY_END_HR   = 21;     // 9 PM
          const HRS_TOTAL    = DAY_END_HR - DAY_START_HR;
          const LABEL_W      = 220;     // driver-name column width
          const PX_PER_HR    = 70;     // 16 hr × 70 = 1120 px wide → scrolls

          // Current time as a fractional hour for the "now" line
          const now = new Date();
          const nowHr = now.getHours() + now.getMinutes()/60;
          const nowInRange = nowHr >= DAY_START_HR && nowHr <= DAY_END_HR;
          const nowX = (nowHr - DAY_START_HR) * PX_PER_HR;

          // Convert "HH:MM" string → fractional hours (or null if absent)
          const parseHHMM = (s) => {
            if (!s || typeof s !== "string") return null;
            const [h,m] = s.split(":").map(Number);
            if (isNaN(h)) return null;
            return h + (m||0)/60;
          };

          // ── Build driver rows ───────────────────────────────────────────
          // One row per non-MAINTENANCE driver across all carriers
          const driverRows = CARRIER_FLEET.flatMap(c =>
            c.tractors
              .filter(t => t.status !== "MAINTENANCE")
              .map(t => {
                // Find this driver's live loads
                const loads = liveLoads.filter(l =>
                  l.truck === t.unit && l.carrier === c.short
                );
                // Build Gantt blocks from the loads
                const blocks = loads.map(l => {
                  // Best-effort timing: use departed→eta if both present,
                  // otherwise place a 60-min block ending at ETA
                  const etaHr = parseHHMM(l.eta);
                  const depHr = parseHHMM(l.departed);
                  let startHr, endHr;
                  if (depHr != null && etaHr != null) {
                    startHr = depHr;
                    endHr   = etaHr;
                  } else if (etaHr != null) {
                    startHr = etaHr - 1;
                    endHr   = etaHr;
                  } else {
                    return null; // can't place — skip
                  }
                  // Clamp to visible window
                  startHr = Math.max(DAY_START_HR, startHr);
                  endHr   = Math.min(DAY_END_HR, endHr);
                  if (endHr <= startHr) return null;
                  return {
                    kind:"live",
                    load:l,
                    startHr, endHr,
                    durHr: endHr - startHr,
                  };
                }).filter(Boolean);
                return { carrier:c, tractor:t, blocks };
              })
          );

          // Color helpers
          const statusColor = (s) => ({
            "LOADING":   "#0D9488",
            "EN ROUTE":  "#0891B2",
            "DELIVERING":"#059669",
            "SCHEDULED": "#EA580C",
          }[s] || C.textMut);

          const hosColor = (hrs) => hrs <= 2 ? "#EF4444" : hrs <= 4 ? "#F59E0B" : "#22C55E";

          // Filter rows by the existing carrier filter
          const visibleRows = carrierFilter === "ALL"
            ? driverRows
            : driverRows.filter(r => r.carrier.short === carrierFilter);

          // KPI strip just above the Gantt
          const totalDrivers = visibleRows.length;
          const driversOnRoute = visibleRows.filter(r =>
            r.blocks.some(b => b.load && ["EN ROUTE","DELIVERING","LOADING"].includes(b.load.status))
          ).length;
          const driversIdle = visibleRows.filter(r => r.blocks.length === 0 && r.tractor.status === "AVAILABLE").length;
          const totalHosLeft = visibleRows.reduce((a,r) => a + (r.tractor.hos || 0), 0);

          return (
            <div style={{display:"flex",flexDirection:"column",gap:12}}>

              {/* ── Day Schedule KPI strip ─────────────────────────────── */}
              <div style={{display:"flex",gap:8}}>
                {[
                  {label:"Drivers on duty",  val:totalDrivers,    sub:"shown on board",          color:C.blue},
                  {label:"Currently rolling",val:driversOnRoute,  sub:"loading + en route + delivering", color:"#0891B2"},
                  {label:"Idle drivers",     val:driversIdle,     sub:"available, no trip yet",  color:driversIdle>2?"#F59E0B":C.green},
                  {label:"HOS hours left",   val:`${Math.round(totalHosLeft)}h`, sub:"across all drivers", color:totalHosLeft>50?C.green:"#F59E0B"},
                ].map((k,i)=><KpiCard key={i} {...k} C={C} darkMode={darkMode} glass={true}/>)}
              </div>

              {/* ── Gantt card ─────────────────────────────────────────── */}
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden"}}>

                {/* Controls */}
                <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",padding:"10px 16px",borderBottom:`1px solid ${C.cardBord}`,gap:8,flexWrap:"wrap"}}>
                  <div style={{display:"flex",alignItems:"center",gap:10}}>
                    <div style={{fontSize:13,fontWeight:800,color:C.textPri,fontFamily:FONT}}>
                      Today's driver schedule
                    </div>
                    <span style={{fontSize:10.5,color:C.textMut,fontFamily:FONT}}>
                      {now.toLocaleDateString("en-US",{weekday:"long",month:"short",day:"numeric"})}
                    </span>
                  </div>
                  <div style={{display:"flex",gap:6,alignItems:"center"}}>
                    {/* Carrier filter (reuses existing state) */}
                    <select value={carrierFilter} onChange={e=>setCarrierFilter(e.target.value)}
                      style={{padding:"4px 8px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textSec,fontSize:10.5,cursor:"pointer",fontFamily:FONT}}>
                      <option value="ALL">All carriers</option>
                      {CARRIER_FLEET.map(c=><option key={c.id} value={c.short}>{c.short}</option>)}
                    </select>
                    {/* Live legend */}
                    <div style={{display:"flex",gap:8,marginLeft:6,fontSize:9.5,color:C.textSec,fontFamily:FONT}}>
                      {[
                        {l:"Loading",   c:"#0D9488"},
                        {l:"En Route",  c:"#0891B2"},
                        {l:"Delivering",c:"#059669"},
                      ].map(x => (
                        <div key={x.l} style={{display:"flex",alignItems:"center",gap:4}}>
                          <div style={{width:9,height:9,borderRadius:2,background:x.c}}/>{x.l}
                        </div>
                      ))}
                    </div>
                  </div>
                </div>

                {/* Scrollable Gantt area */}
                <div style={{overflowX:"auto",overflowY:"visible"}}>
                  <div style={{minWidth:LABEL_W + HRS_TOTAL*PX_PER_HR + 20, position:"relative"}}>

                    {/* Time-axis header */}
                    <div style={{
                      display:"flex",
                      borderBottom:`1px solid ${C.cardBord}`,
                      background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                      position:"sticky", top:0, zIndex:5,
                    }}>
                      <div style={{
                        width:LABEL_W, flexShrink:0,
                        padding:"8px 12px",
                        borderRight:`1px solid ${C.cardBord}`,
                        fontSize:9, fontWeight:800, color:C.textMut,
                        letterSpacing:.6, textTransform:"uppercase",
                        fontFamily:FONT,
                        display:"flex", alignItems:"center", justifyContent:"space-between",
                      }}>
                        <span>Driver · Truck</span>
                        <span>HOS</span>
                      </div>
                      <div style={{position:"relative", height:32, flex:1}}>
                        {Array.from({length:HRS_TOTAL+1}, (_,i) => {
                          const h = DAY_START_HR + i;
                          const hLabel = h === 0 ? "12 AM"
                                       : h < 12 ? `${h} AM`
                                       : h === 12 ? "12 PM"
                                       : `${h-12} PM`;
                          return (
                            <div key={i} style={{
                              position:"absolute", left:i*PX_PER_HR, top:0,
                              width:PX_PER_HR, height:"100%",
                              borderLeft: i > 0 ? `1px solid ${C.cardBord}` : "none",
                              fontSize:9.5, fontWeight:700, color:C.textMut,
                              fontFamily:"Arial,sans-serif",
                              display:"flex", alignItems:"center", paddingLeft:6,
                            }}>{hLabel}</div>
                          );
                        })}
                      </div>
                    </div>

                    {/* Driver rows */}
                    {visibleRows.length === 0 ? (
                      <div style={{padding:"40px 20px", textAlign:"center", color:C.textMut, fontSize:12, fontFamily:FONT}}>
                        No drivers match this filter.
                      </div>
                    ) : visibleRows.map((row,ri) => {
                      const t = row.tractor;
                      const c = row.carrier;
                      const hos = t.hos || 0;
                      const hosPct = Math.min(1, hos / 14); // 14 = max DOT HOS
                      const hosCol = hosColor(hos);
                      const isLast = ri === visibleRows.length - 1;
                      return (
                        <div key={`${c.id}-${t.id}`} style={{
                          display:"flex",
                          borderBottom: isLast ? "none" : `1px solid ${C.cardBord}`,
                          background: ri % 2 === 1
                            ? (darkMode?"rgba(255,255,255,.015)":"#FCFCFD")
                            : "transparent",
                        }}>
                          {/* Driver label */}
                          <div style={{
                            width:LABEL_W, flexShrink:0, padding:"10px 12px",
                            borderRight:`1px solid ${C.cardBord}`,
                            display:"flex", flexDirection:"column", gap:5,
                          }}>
                            <div style={{display:"flex",justifyContent:"space-between",alignItems:"baseline",gap:6}}>
                              <div style={{minWidth:0,flex:1}}>
                                <div style={{fontSize:11.5,fontWeight:700,color:C.textPri,fontFamily:FONT,
                                  overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>
                                  {t.driver}
                                </div>
                                <div style={{fontSize:9.5,color:C.textMut,fontFamily:FONT,marginTop:1}}>
                                  {c.short} · {t.unit}
                                </div>
                              </div>
                              <div style={{fontSize:10.5,fontWeight:800,color:hosCol,fontFamily:"Arial,sans-serif",whiteSpace:"nowrap"}}>
                                {hos.toFixed(1)}h
                              </div>
                            </div>
                            {/* HOS bar */}
                            <div style={{height:4,background:darkMode?"rgba(255,255,255,.06)":"#E5E9EF",borderRadius:2,overflow:"hidden"}}>
                              <div style={{height:"100%",width:`${hosPct*100}%`,background:hosCol,borderRadius:2}}/>
                            </div>
                          </div>

                          {/* Timeline cells */}
                          <div style={{position:"relative", flex:1, minHeight:60}}>
                            {/* Hour grid lines */}
                            {Array.from({length:HRS_TOTAL+1}, (_,i) => i > 0 && (
                              <div key={i} style={{
                                position:"absolute",
                                left:i*PX_PER_HR, top:0, bottom:0, width:1,
                                background: i % 6 === 0
                                  ? (darkMode?"rgba(255,255,255,.06)":"#E5E9EF")
                                  : (darkMode?"rgba(255,255,255,.03)":"#F0F2F5"),
                              }}/>
                            ))}

                            {/* Trip blocks */}
                            {row.blocks.map((b,bi) => {
                              const left  = (b.startHr - DAY_START_HR) * PX_PER_HR;
                              const width = b.durHr * PX_PER_HR;
                              const col   = statusColor(b.load.status);
                              return (
                                <div key={bi}
                                  title={`${b.load.id} · ${b.load.status}\n${b.load.origin} → ${b.load.dest}\n${b.load.gals.toLocaleString()} gal ${b.load.grade}\nETA ${b.load.eta}`}
                                  onClick={() => { setSelectedLoad(b.load); }}
                                  style={{
                                    position:"absolute",
                                    left, width, top:8, height:44,
                                    borderRadius:6,
                                    background: `linear-gradient(180deg, ${col}E0, ${col}A0)`,
                                    border:`1px solid ${col}`,
                                    color:"#fff",
                                    cursor:"pointer",
                                    overflow:"hidden",
                                    padding:"4px 8px",
                                    display:"flex", flexDirection:"column", justifyContent:"center",
                                    boxShadow:"0 1px 3px rgba(0,0,0,.18)",
                                    transition:"transform .12s, box-shadow .12s",
                                  }}
                                  onMouseEnter={e=>{e.currentTarget.style.transform="translateY(-1px)";e.currentTarget.style.boxShadow="0 4px 10px rgba(0,0,0,.25)";}}
                                  onMouseLeave={e=>{e.currentTarget.style.transform="none";e.currentTarget.style.boxShadow="0 1px 3px rgba(0,0,0,.18)";}}>
                                  <div style={{fontSize:10,fontWeight:800,letterSpacing:.4,opacity:.95,fontFamily:"Arial,sans-serif",
                                    overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>
                                    {b.load.id} · {b.load.status}
                                  </div>
                                  <div style={{fontSize:9.5,fontWeight:600,opacity:.9,fontFamily:FONT,
                                    overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>
                                    → {b.load.dest}
                                  </div>
                                  {width > 80 && (
                                    <div style={{fontSize:9,opacity:.85,fontFamily:"Arial,sans-serif",
                                      overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>
                                      {(b.load.gals/1000).toFixed(0)}K {b.load.grade.charAt(0)} · ETA {b.load.eta}
                                    </div>
                                  )}
                                </div>
                              );
                            })}

                            {/* Empty-row hint when driver has no trips */}
                            {row.blocks.length === 0 && (
                              <div style={{
                                position:"absolute", left:8, top:"50%", transform:"translateY(-50%)",
                                fontSize:10, color:C.textMut, fontStyle:"italic", fontFamily:FONT,
                              }}>
                                {t.status === "AVAILABLE" ? "Available — no trip scheduled" : t.status}
                              </div>
                            )}
                          </div>
                        </div>
                      );
                    })}

                    {/* "Now" vertical line — overlays all rows */}
                    {nowInRange && (
                      <div style={{
                        position:"absolute",
                        left: LABEL_W + nowX,
                        top: 32, bottom: 0, width: 2,
                        background:"#EF4444",
                        boxShadow:"0 0 4px rgba(239,68,68,.6)",
                        pointerEvents:"none", zIndex:4,
                      }}>
                        <div style={{
                          position:"absolute", top:-8, left:-22,
                          background:"#EF4444", color:"#fff",
                          fontSize:9, fontWeight:800, padding:"2px 6px", borderRadius:3,
                          fontFamily:"Arial,sans-serif", letterSpacing:.4,
                          whiteSpace:"nowrap",
                        }}>
                          NOW {now.toLocaleTimeString("en-US",{hour:"numeric",minute:"2-digit",hour12:true})}
                        </div>
                      </div>
                    )}
                  </div>
                </div>
              </div>

              {/* ── Honest scope footnote ───────────────────────────────── */}
              <div style={{
                padding:"10px 14px", borderRadius:8,
                background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                border:`1px solid ${C.cardBord}`,
                fontSize:10.5, color:C.textSec, fontFamily:FONT, lineHeight:1.5,
              }}>
                <span style={{fontWeight:800, color:C.textPri, letterSpacing:.5}}>About this view</span>
                <span style={{opacity:.7, marginLeft:6}}>
                  Hourly schedule for every driver on duty today. Trip blocks are placed using each load's
                  recorded depart and ETA times; click a block to open the load detail. The red NOW line
                  shows real wall-clock time. Drag-to-reschedule and "assign trip from queue" actions are
                  next-iteration — for now use the Plan tab to dispatch new loads, then they appear here
                  once they're in the live feed.
                </span>
              </div>
            </div>
          );
        })()}

        {/*  FLEET & DRIVERS  */}
        {dispatchTab==="fleet" && (
          <div style={{display:"flex",flexDirection:"column",gap:12}}>

            {/* Summary KPI strip */}
            {(()=>{
              const allTractors = CARRIER_FLEET.flatMap(c=>c.tractors);
              const byStatus = s => allTractors.filter(t=>t.status===s).length;
              return (
                <div style={{display:"flex",gap:8}}>
                  {[
                    {label:"Total Drivers",    val:allTractors.length,           color:C.textPri, sub:`across ${CARRIER_FLEET.length} carriers`},
                    {label:"Available",        val:byStatus("AVAILABLE"),         color:"#059669",  sub:"ready to dispatch"},
                    {label:"On Load",          val:byStatus("LOADING")+byStatus("EN ROUTE")+byStatus("DELIVERING"), color:"#0891B2", sub:"loading + in transit"},
                    {label:"HOS Reset",        val:byStatus("HOS RESET"),         color:"#64748B",  sub:"10-hr rest break"},
                    {label:"Maintenance",      val:byStatus("MAINTENANCE"),        color:C.red,      sub:"out of service"},
                  ].map((k,i)=><KpiCard key={i} {...k} C={C} darkMode={darkMode} glass={true}/>)}
                </div>
              );
            })()}

            {/* Master driver roster — all drivers flat, with carrier attribution */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden"}}>
              <div style={{padding:"12px 16px",borderBottom:`1px solid ${C.cardBord}`,display:"flex",alignItems:"center",justifyContent:"space-between"}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT}}>Driver & Truck Roster — All {CARRIER_FLEET.reduce((a,c)=>a+c.tractors.length,0)} Drivers</div>
                <div style={{fontSize:10,color:C.textSec,fontFamily:FONT}}>Sorted by carrier · HOS as of 09:22 CT</div>
              </div>

              {/* Column headers */}
              <div style={{display:"grid",gridTemplateColumns:"36px 1fr 140px 120px 180px 90px 90px 100px 100px",gap:"0 8px",padding:"7px 16px",background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC",borderBottom:`1px solid ${C.cardBord}`}}>
                {["","Driver","Carrier","Unit","Location","Status","HOS","Odometer","Last Inspect"].map((h,i)=>(
                  <div key={i} style={{fontSize:8.5,fontWeight:700,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</div>
                ))}
              </div>

              {/* All drivers */}
              {CARRIER_FLEET.map((carrier,ci)=>
                carrier.tractors.map((t,ti)=>{
                  const isFirst = ti===0;
                  const hosCol  = t.hos>=8?"#059669":t.hos>=4?"#F59E0B":"#EF4444";
                  const hosPct  = Math.min(1,t.hos/11);
                  const initials= t.driver.split(" ").map(n=>n[0]).join("");
                  const rowBg   = t.status==="MAINTENANCE"?(darkMode?"rgba(239,68,68,.04)":"#FFF8F8"):t.status==="HOS RESET"?(darkMode?"rgba(100,116,139,.06)":"#F9FAFB"):"transparent";
                  return (
                    <div key={t.id}>
                      {/* Carrier group separator */}
                      {isFirst&&(
                        <div style={{padding:"6px 16px",background:darkMode?"rgba(200,164,74,.06)":"#F8FAFB",borderTop:`1px solid ${C.cardBord}`,borderBottom:`1px solid ${C.cardBord}`,display:"flex",alignItems:"center",gap:10}}>
                          <span style={{fontSize:10,fontWeight:800,color:C.gold,fontFamily:FONT,textTransform:"uppercase",letterSpacing:.6}}>{carrier.name}</span>
                          <span style={{fontSize:9.5,color:C.textMut}}>DOT {carrier.dot} · {carrier.mc} · SCAC {carrier.scac} · {carrier.available}/{carrier.trucks} avail</span>
                          <span style={{marginLeft:"auto",fontSize:9.5,fontWeight:700,color:C.gold}}> {carrier.rating}</span>
                        </div>
                      )}
                      <div style={{display:"grid",gridTemplateColumns:"36px 1fr 140px 120px 180px 90px 90px 100px 100px",gap:"0 8px",padding:"9px 16px",borderBottom:`1px solid ${C.cardBord}`,background:rowBg,alignItems:"center"}}>

                        {/* Avatar */}
                        <div style={{width:30,height:30,borderRadius:"50%",background:"#F4D398",display:"flex",alignItems:"center",justifyContent:"center",fontSize:10.5,fontWeight:800,color:"#0D1B2A",flexShrink:0,letterSpacing:-.5}}>
                          {initials}
                        </div>

                        {/* Driver name */}
                        <div>
                          <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{t.driver}</div>
                          <div style={{fontSize:9.5,color:C.textMut,marginTop:1}}>{carrier.short} · {t.id}</div>
                        </div>

                        {/* Carrier */}
                        <div style={{fontSize:10.5,color:C.textSec,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{carrier.name}</div>

                        {/* Unit */}
                        <div style={{fontSize:11,fontWeight:700,color:C.gold,fontFamily:FONT}}>{t.unit}</div>

                        {/* Location */}
                        <div style={{fontSize:10,color:C.textSec,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{t.location}</div>

                        {/* Status */}
                        <div>
                          <span style={{fontSize:9,fontWeight:700,padding:"2px 7px",borderRadius:8,background:statusBg(t.status),color:statusColor(t.status),border:`1px solid ${statusColor(t.status)}30`,whiteSpace:"nowrap",display:"inline-block"}}>{t.status}</span>
                        </div>

                        {/* HOS bar + value */}
                        <div style={{display:"flex",alignItems:"center",gap:5}}>
                          <div style={{flex:1,height:5,background:C.cardBord,borderRadius:2,overflow:"hidden",minWidth:32}}>
                            <div style={{height:"100%",width:`${hosPct*100}%`,background:hosCol,borderRadius:2}}/>
                          </div>
                          <span style={{fontSize:10.5,fontWeight:700,color:hosCol,fontFamily:FONT,whiteSpace:"nowrap"}}>{t.hos}h</span>
                        </div>

                        {/* Odometer */}
                        <div style={{fontSize:10.5,color:C.textSec,fontFamily:FONT}}>{t.odometer.toLocaleString()}</div>

                        {/* Last inspect */}
                        <div style={{fontSize:10.5,color:C.textSec}}>{t.lastInspect}</div>
                      </div>
                    </div>
                  );
                })
              )}
            </div>

            {/* Carrier compliance + contract summary */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}>Carrier Summary — Rates, Compliance & YTD Performance</div>
              <div style={{overflowX:"auto"}}>
                <table style={{width:"100%",borderCollapse:"collapse",minWidth:900}}>
                  <thead>
                    <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                      {["Carrier","SCAC","Trucks","Base Rate","Per-Mile","Detention/hr","Contract Expiry","HazMat","Vapor Rec.","Rating","YTD Loads","YTD O/S gal","Alerts"].map(h=>(
                        <th key={h} style={{padding:"7px 10px",fontSize:8.5,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {CARRIER_FLEET.map((c,i)=>{
                      const alerts = c.alerts||[];
                      return (
                        <tr key={c.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:alerts.length>0?(darkMode?"rgba(251,191,36,.04)":"#F8FAFB"):(i%2===0?"transparent":darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)")}}>
                          <td style={{padding:"8px 10px"}}>
                            <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{c.name}</div>
                            <div style={{fontSize:9.5,color:C.textMut}}>DOT {c.dot}</div>
                          </td>
                          <td style={{padding:"8px 10px",fontSize:10.5,fontWeight:700,color:C.gold,fontFamily:FONT}}>{c.scac}</td>
                          <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{c.available}/{c.trucks}</td>
                          <td style={{padding:"8px 10px",fontSize:11,color:C.textPri,fontFamily:FONT}}>${c.rateBase.toFixed(4)}<span style={{color:C.textMut,fontSize:9.5}}> /gal</span></td>
                          <td style={{padding:"8px 10px",fontSize:11,color:C.textPri,fontFamily:FONT}}>${c.ratePerMile.toFixed(2)}<span style={{color:C.textMut,fontSize:9.5}}> /mi</span></td>
                          <td style={{padding:"8px 10px",fontSize:11,color:C.textPri,fontFamily:FONT}}>${c.detentionRate}/hr</td>
                          <td style={{padding:"8px 10px",fontSize:10.5,color:new Date(c.contractExpiry.replace("Dec","2025-12").replace("Sep","2025-09").replace("Jun","2025-06").replace("Mar","2026-03"))<new Date("2025-07-01")?C.amber:C.textSec}}>{c.contractExpiry}</td>
                          <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:c.hazmatCert?"#059669":"#EF4444"}}>{c.hazmatCert?"":""}</td>
                          <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:c.vaporRecovery?"#059669":"#F59E0B"}}>{c.vaporRecovery?"":""}</td>
                          <td style={{padding:"8px 10px",fontSize:12,fontWeight:800,color:c.rating>=4.5?C.green:c.rating>=4.0?C.amber:C.red,fontFamily:FONT}}> {c.rating}</td>
                          <td style={{padding:"8px 10px",fontSize:11,color:C.textPri,fontFamily:FONT}}>{c.ytdLoads}</td>
                          <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:c.ytdOverShort<-50?C.red:c.ytdOverShort>50?C.amber:C.green,fontFamily:FONT}}>{c.ytdOverShort>0?"+":""}{c.ytdOverShort}</td>
                          <td style={{padding:"8px 10px"}}>
                            {alerts.length>0
                              ? <span style={{fontSize:9.5,color:C.amber,fontWeight:700}}> {alerts.length} alert{alerts.length>1?"s":""}</span>
                              : <span style={{fontSize:9.5,color:"#059669"}}> Clear</span>}
                          </td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            </div>

          </div>
        )}

        {/*  LOAD PLANNING  */}
        {/*  LOAD PLANNING  */}
        {dispatchTab==="loads" && (
          <div style={{display:"flex",flexDirection:"column",gap:12}}>

            {/* Compartment optimization guide */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Compartment Optimization — Split Load Matching</div>
              <div style={{fontSize:10.5,color:C.textSec,marginBottom:14}}>Match truck compartments to store needs. Red = compartment too large (deadhead gal). Green = good fit.</div>
              <div style={{overflowX:"auto"}}>
                <table style={{width:"100%",borderCollapse:"collapse",minWidth:800}}>
                  <thead>
                    <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                      {["Carrier / Truck","Compartments","Avail Now","Suggested Load — Store + Grade + Vol","Fit Score","Deadhead gal","Est. Cost","Action"].map(h=>(
                        <th key={h} style={{padding:"7px 10px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {CARRIER_FLEET.flatMap(c=>
                      c.tractors.filter(t=>t.status==="AVAILABLE").map(t=>({carrier:c,tractor:t}))
                    ).slice(0,12).map(({carrier,tractor},ri)=>{
                      const urgStore = pendingLoads[ri%pendingLoads.length];
                      const store = STORES.find(s=>s.id===urgStore?.storeId);
                      const grade = GRADES.find(g=>urgStore?.forecast[g]?.daysToReorder<=3)||"Regular";
                      const needVol = Math.round((store?.tanks?.[grade]||10000)*0.78/500)*500;
                      const bestComp = carrier.compartments.reduce((best,c)=>Math.abs(c-needVol)<Math.abs(best-needVol)?c:best,carrier.compartments[0]);
                      const deadhead = Math.max(0, bestComp - needVol);
                      const fit = deadhead===0?100:Math.round((1-deadhead/bestComp)*100);
                      const estMiles = 45; // typical one-way distance for urgent reorder
                      const estCost = (needVol * carrier.rateBase + estMiles * carrier.ratePerMile).toFixed(0);
                      return (
                        <tr key={`${carrier.id}-${tractor.id}`} style={{borderBottom:`1px solid ${C.cardBord}`,background:ri%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)")}}>
                          <td style={{padding:"8px 10px"}}>
                            <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{carrier.short} — {tractor.unit}</div>
                            <div style={{fontSize:9.5,color:C.textSec}}>{tractor.driver} · HOS {tractor.hos}h</div>
                          </td>
                          <td style={{padding:"8px 10px",fontSize:10.5,color:C.textSec,whiteSpace:"nowrap"}}>{carrier.compartments.map(x=>`${(x/1000).toFixed(0)}K`).join(" | ")}</td>
                          <td style={{padding:"8px 10px"}}>
                            <span style={{fontSize:9.5,fontWeight:700,color:C.green}}> Ready</span>
                          </td>
                          <td style={{padding:"8px 10px",maxWidth:220}}>
                            <div style={{fontSize:11,fontWeight:600,color:C.textPri,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{store?.name||"—"}</div>
                            <div style={{fontSize:9.5,color:C.textSec}}>{grade} · {needVol.toLocaleString()} gal needed</div>
                          </td>
                          <td style={{padding:"8px 10px"}}>
                            <div style={{display:"flex",alignItems:"center",gap:6}}>
                              <div style={{width:36,height:6,background:C.cardBord,borderRadius:3,overflow:"hidden"}}>
                                <div style={{height:"100%",width:`${fit}%`,background:fit>=90?C.green:fit>=70?C.amber:C.red,borderRadius:3}}/>
                              </div>
                              <span style={{fontSize:10.5,fontWeight:700,color:fit>=90?C.green:fit>=70?C.amber:C.red,fontFamily:FONT}}>{fit}%</span>
                            </div>
                          </td>
                          <td style={{padding:"8px 10px",fontSize:11,color:deadhead>0?C.amber:C.green,fontWeight:700,fontFamily:FONT}}>{deadhead>0?deadhead.toLocaleString():"—"}</td>
                          <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${parseInt(estCost).toLocaleString()}</td>
                          <td style={{padding:"8px 10px"}}>
                            <button style={{fontSize:9.5,padding:"4px 10px",borderRadius:5,border:`1px solid ${C.gold}`,background:darkMode?"rgba(200,164,74,.12)":"#FFF9E6",color:C.gold,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                              Assign Load
                            </button>
                          </td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            </div>

            {/* Fuel surcharge calculator */}
            <div style={{display:"flex",gap:12}}>
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}> Fuel Surcharge Calculator</div>
                <div style={{fontSize:10.5,color:C.textSec,marginBottom:10}}>Surcharge = (Current diesel rack − base price) × miles × factor</div>
                {CARRIER_FLEET.map(c=>{
                  // Fuel surcharge: industry-standard formula is (current_diesel - base_diesel) / avg_MPG
                  // where carriers run ~6 MPG on Class 8 tankers. Base is the contract-start price.
                  const baseDiesel = 4.00;
                  const currDiesel = RACK_PRICES.selma.Diesel;
                  const MPG = 6.0;
                  const surcharge  = Math.max(0, (currDiesel - baseDiesel) / MPG);
                  return (
                    <div key={c.id} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"7px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                      <span style={{fontSize:11,color:C.textPri,fontFamily:FONT}}>{c.short} — {c.name}</span>
                      <div style={{display:"flex",gap:16,textAlign:"right"}}>
                        <div>
                          <div style={{fontSize:10.5,fontWeight:700,color:C.amber,fontFamily:FONT}}>${surcharge.toFixed(4)}/mi</div>
                          <div style={{fontSize:9,color:C.textMut}}>surcharge</div>
                        </div>
                        <div>
                          <div style={{fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${(c.ratePerMile+surcharge).toFixed(4)}/mi</div>
                          <div style={{fontSize:9,color:C.textMut}}>all-in rate</div>
                        </div>
                      </div>
                    </div>
                  );
                })}
              </div>

              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}> IFTA / Mileage Summary — Q1 2025</div>
                {[
                  {label:"Total Miles Operated",  val:"412,840 mi"},
                  {label:"Fuel Consumed (diesel)", val:"68,940 gal"},
                  {label:"Miles per Gallon",       val:"5.99 mpg"},
                  {label:"IFTA Tax Owed — NC",     val:"$14,280"},
                  {label:"IFTA Tax Owed — SC",     val:"$8,640"},
                  {label:"IFTA Tax Owed — VA",     val:"$6,120"},
                  {label:"IFTA Tax Owed — GA",     val:"$5,880"},
                  {label:"IFTA Tax Owed — FL",     val:"$7,440"},
                  {label:"Q1 Filing Deadline",     val:"Apr 30, 2025"},
                ].map((row,ri)=>(
                  <div key={ri} style={{display:"flex",justifyContent:"space-between",padding:"6px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                    <span style={{fontSize:10.5,color:C.textSec}}>{row.label}</span>
                    <span style={{fontSize:10.5,fontWeight:700,color:row.label.includes("Deadline")?C.amber:C.textPri,fontFamily:FONT}}>{row.val}</span>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/*  TERMINAL STATUS  */}
        {dispatchTab==="terminal" && (
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            <div style={{display:"grid",gridTemplateColumns:"repeat(3,1fr)",gap:12}}>
              {TERMINALS.map(t=>{
                const ts  = TERMINAL_STATUS[t.id];
                const win = COLONIAL.terminalWindows[t.id];
                const cColor = ts.congestion==="LOW"?C.green:ts.congestion==="MODERATE"?C.amber:C.red;
                const loadsHere = ACTIVE_LOADS.filter(l=>l.origin.includes(t.name.split(",")[0]));
                return (
                  <div key={t.id} style={{background:C.cardBg,border:`2px solid ${ts.congestion==="HIGH"?C.red:C.cardBord}`,borderRadius:10,padding:16}}>
                    <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:10}}>
                      <div>
                        <div style={{fontSize:13,fontWeight:800,color:C.textPri,fontFamily:FONT,display:"flex",alignItems:"center",gap:6}}><ZoneBadge terminalId={t.id} size="lg"/>{t.short} — {t.name}</div>
                        <div style={{fontSize:10,color:C.textSec,marginTop:1}}>{t.pipeline} · {t.supplier}</div>
                      </div>
                      <span style={{fontSize:10,fontWeight:700,padding:"3px 10px",borderRadius:10,background:`${cColor}18`,color:cColor,border:`1px solid ${cColor}30`}}>{ts.congestion}</span>
                    </div>

                    <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:8,marginBottom:12}}>
                      {[
                        {l:"Rack Wait",    v:`${ts.rackWait} min`,  color:ts.rackWait>30?C.red:ts.rackWait>15?C.amber:C.green},
                        {l:"Next Slot",    v:ts.nextAvail,           color:C.textPri},
                        {l:"Last Load",    v:ts.lastLoad,            color:C.textSec},
                        {l:"Loads Today",  v:loadsHere.length,       color:C.blue},
                      ].map((s,si)=>(
                        <div key={si} style={{padding:"8px 10px",borderRadius:7,background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC"}}>
                          <div style={{fontSize:9,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,marginBottom:2}}>{s.l}</div>
                          <div style={{fontSize:15,fontWeight:800,color:s.color,fontFamily:FONT}}>{s.v}</div>
                        </div>
                      ))}
                    </div>

                    {/* Lane visualization */}
                    <div style={{marginBottom:10}}>
                      <div style={{fontSize:9,color:C.textMut,marginBottom:4}}>RACK LANES</div>
                      <div style={{display:"flex",gap:4}}>
                        {Array.from({length:ts.lanesTotal}).map((_,li)=>(
                          <div key={li} style={{flex:1,height:24,borderRadius:4,background:li<ts.lanesOpen?C.green:(darkMode?"rgba(239,68,68,.35)":"#FCA5A5"),display:"flex",alignItems:"center",justifyContent:"center",fontSize:9,fontWeight:700,color:li<ts.lanesOpen?"#fff":"#DC2626"}}>
                            {li+1}
                          </div>
                        ))}
                      </div>
                      <div style={{fontSize:9.5,color:C.textMut,marginTop:4}}>{ts.lanesOpen} of {ts.lanesTotal} lanes open</div>
                    </div>

                    {/* Cycle window */}
                    <div style={{padding:"8px 10px",borderRadius:7,background:win?.daysToWindow===0?(darkMode?"rgba(34,197,94,.12)":"#F0FDF4"):(darkMode?"rgba(107,114,128,.06)":"#F8FAFC"),border:`1px solid ${win?.daysToWindow===0?C.green:C.cardBord}`}}>
                      <div style={{fontSize:9,color:C.textMut,marginBottom:2}}>PIPELINE WINDOW</div>
                      <div style={{fontSize:12,fontWeight:700,color:win?.daysToWindow===0?C.green:C.textPri,fontFamily:FONT}}>
                        {win?.daysToWindow===0?" Open Now":`Opens in ${win?.daysToWindow} days`}
                      </div>
                    </div>

                    {/* Colonial tariff */}
                    <div style={{marginTop:10,fontSize:9.5,color:C.textSec}}>
                      Tariff: Gas ${COLONIAL.tariffs[t.id]?.gasoline?.toFixed(4)} · Dist ${COLONIAL.tariffs[t.id]?.distillate?.toFixed(4)} /gal
                    </div>
                  </div>
                );
              })}
            </div>

            {/* BOL / Meter Ticket Log */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}> Active BOL / Meter Tickets</div>
              <div style={{overflowX:"auto"}}>
                <table style={{width:"100%",borderCollapse:"collapse",minWidth:700}}>
                  <thead>
                    <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                      {["Load ID","BOL #","Carrier","Origin","Destination","Grade","Gallons","Basement Ticket","Temp °F","API Gravity","Status"].map(h=>(
                        <th key={h} style={{padding:"6px 8px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.3,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {ACTIVE_LOADS.map((ld,i)=>(
                      <tr key={ld.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:i%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)")}}>
                        <td style={{padding:"7px 8px",fontSize:10.5,fontWeight:700,color:C.gold,fontFamily:FONT}}>{ld.id}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,fontFamily:FONT}}>{ld.bol||"Pending"}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textPri}}>{ld.carrier}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{ld.origin}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,maxWidth:140,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{ld.dest}</td>
                        <td style={{padding:"7px 8px"}}><GradeTag grade={ld.grade} darkMode={darkMode}/></td>
                        <td style={{padding:"7px 8px",fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{ld.gals.toLocaleString()}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{ld.bsmtTicket||"—"}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:ld.tempF?(ld.tempF>75?C.amber:C.textPri):C.textMut}}>{ld.tempF||"—"}</td>
                        <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{ld.apiGravity||"—"}</td>
                        <td style={{padding:"7px 8px"}}>
                          <span style={{fontSize:9.5,fontWeight:700,padding:"2px 7px",borderRadius:8,background:statusBg(ld.status),color:statusColor(ld.status),border:`1px solid ${statusColor(ld.status)}30`}}>{ld.status}</span>
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          </div>
        )}

        {/*  DETENTION & O/S  */}
        {dispatchTab==="detention" && (
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            <div style={{display:"flex",gap:12}}>

              {/* Detention log */}
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}>Detention Log — Last 5 Days</div>
                <div style={{fontSize:10.5,color:C.textSec,marginBottom:12}}>
                  Total: ${DETENTION_LOG.reduce((a,d)=>a+d.cost,0)} · {DETENTION_LOG.reduce((a,d)=>a+d.mins,0)} minutes · Free time: 30 min standard
                </div>
                <table style={{width:"100%",borderCollapse:"collapse"}}>
                  <thead>
                    <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                      {["Date","Carrier","Unit","Site","Minutes","Cause","Cost"].map(h=>(
                        <th key={h} style={{padding:"6px 8px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.3,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {DETENTION_LOG.map((d,i)=>{
                      const severe = d.mins > 60;
                      return (
                        <tr key={i} style={{borderBottom:`1px solid ${C.cardBord}`,background:severe?(darkMode?"rgba(239,68,68,.06)":"#FFF5F5"):"transparent"}}>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{d.date}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{d.carrier}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{d.truck}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textPri,maxWidth:140,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{d.site}</td>
                          <td style={{padding:"7px 8px",fontSize:12,fontWeight:800,color:severe?C.red:d.mins>30?C.amber:C.textPri,fontFamily:FONT}}>{d.mins}m</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,maxWidth:200,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{d.cause}</td>
                          <td style={{padding:"7px 8px",fontSize:11,fontWeight:700,color:severe?C.red:C.amber,fontFamily:FONT}}>${d.cost}</td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>

                {/* Detention by carrier summary */}
                <div style={{marginTop:14}}>
                  <div style={{fontSize:10,fontWeight:700,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,marginBottom:8}}>By Carrier</div>
                  {CARRIER_FLEET.map(c=>{
                    const incidents = DETENTION_LOG.filter(d=>d.carrier===c.short);
                    const total = incidents.reduce((a,d)=>a+d.cost,0);
                    const mins  = incidents.reduce((a,d)=>a+d.mins,0);
                    if(!incidents.length) return null;
                    return (
                      <div key={c.id} style={{display:"flex",justifyContent:"space-between",padding:"5px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                        <span style={{fontSize:11,color:C.textPri,fontFamily:FONT}}>{c.short} — {c.name}</span>
                        <div style={{display:"flex",gap:16}}>
                          <span style={{fontSize:10.5,color:C.textSec}}>{incidents.length} incident{incidents.length!==1?"s":""} · {mins} min</span>
                          <span style={{fontSize:11,fontWeight:700,color:total>100?C.red:C.amber,fontFamily:FONT}}>${total}</span>
                        </div>
                      </div>
                    );
                  })}
                </div>
              </div>

              {/* Over/Short reconciliation */}
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Over/Short Reconciliation</div>
                <div style={{fontSize:10.5,color:C.textSec,marginBottom:12}}>
                  Tolerance: ±0.5% of load volume (±0.003 CPG). Flagged variances trigger meter audit.
                </div>
                <table style={{width:"100%",borderCollapse:"collapse"}}>
                  <thead>
                    <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                      {["Date","BOL #","Carrier","Site","Grade","BOL Gal","Delivered","Variance","$/gal","Cause / Status"].map(h=>(
                        <th key={h} style={{padding:"6px 8px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:["BOL Gal","Delivered","Variance","$/gal"].includes(h)?"right":"left",textTransform:"uppercase",letterSpacing:.3,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {OVERSHORT_LOG.map((row,i)=>{
                      const flagged = row.cause.includes("");
                      const isOver  = row.variance>0;
                      return (
                        <tr key={i} style={{borderBottom:`1px solid ${C.cardBord}`,background:flagged?(darkMode?"rgba(239,68,68,.07)":"#FFF5F5"):"transparent"}}>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec}}>{row.date}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.gold,fontFamily:FONT,whiteSpace:"nowrap"}}>{row.bol}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{row.carrier}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,maxWidth:120,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{row.site}</td>
                          <td style={{padding:"7px 8px"}}><GradeTag grade={row.grade} darkMode={darkMode}/></td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,textAlign:"right"}}>{row.bol_gals.toLocaleString()}</td>
                          <td style={{padding:"7px 8px",fontSize:10.5,color:C.textSec,textAlign:"right"}}>{row.delivered.toLocaleString()}</td>
                          <td style={{padding:"7px 8px",textAlign:"right",fontSize:12,fontWeight:800,color:row.variance===0?C.green:flagged?C.red:C.amber,fontFamily:FONT}}>
                            {row.variance===0?"—":row.variance>0?"+":""}{row.variance}
                          </td>
                          <td style={{padding:"7px 8px",textAlign:"right",fontSize:10.5,fontWeight:700,color:row.variance===0?C.green:flagged?C.red:C.amber,fontFamily:FONT}}>
                            {row.varCPG===0?"—":`${row.varCPG>0?"+":""}${row.varCPG.toFixed(4)}`}
                          </td>
                          <td style={{padding:"7px 8px",fontSize:10,color:flagged?C.red:C.textSec,fontWeight:flagged?700:400,maxWidth:180,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{row.cause}</td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            </div>
          </div>
        )}

        {/*  COMPLIANCE  */}
        {dispatchTab==="compliance" && (
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            <div style={{display:"flex",gap:12}}>

              {/* HOS compliance */}
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Hours of Service (HOS) — All Drivers</div>
                <div style={{fontSize:10.5,color:C.textSec,marginBottom:12}}>FMCSA Rule: 11-hr drive limit · 14-hr on-duty window · 30-min break after 8 hrs · 70-hr/8-day limit</div>
                {CARRIER_FLEET.map(c=>(
                  <div key={c.id} style={{marginBottom:14}}>
                    <div style={{fontSize:11,fontWeight:700,color:C.gold,fontFamily:FONT,marginBottom:6}}>{c.name}</div>
                    {c.tractors.map(t=>{
                      const hosCol = t.hos>=8?C.green:t.hos>=4?C.amber:t.status==="MAINTENANCE"||t.status==="HOS RESET"?C.textMut:C.red;
                      const pct = Math.min(1,t.hos/11);
                      const needsBreak = t.hos<3 && t.status==="EN ROUTE";
                      return (
                        <div key={t.id} style={{display:"flex",alignItems:"center",gap:10,padding:"5px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                          <div style={{width:60,fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT,flexShrink:0}}>{t.unit}</div>
                          <div style={{width:120,fontSize:10.5,color:C.textSec,flexShrink:0,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{t.driver}</div>
                          <div style={{flex:1,height:8,background:C.cardBord,borderRadius:4,overflow:"hidden"}}>
                            <div style={{height:"100%",width:`${pct*100}%`,background:hosCol,borderRadius:4,transition:"width .3s"}}/>
                          </div>
                          <div style={{width:40,textAlign:"right",fontSize:11,fontWeight:700,color:hosCol,fontFamily:FONT,flexShrink:0}}>{t.hos}h</div>
                          <div style={{width:130,flexShrink:0}}>
                            {t.status==="MAINTENANCE"&&<span style={{fontSize:9.5,color:C.red}}> Maintenance</span>}
                            {t.status==="HOS RESET"&&<span style={{fontSize:9.5,color:"#8B5CF6"}}> Reset</span>}
                            {needsBreak&&<span style={{fontSize:9.5,color:C.red,fontWeight:700}}> Break required!</span>}
                            {t.status==="EN ROUTE"&&!needsBreak&&<span style={{fontSize:9.5,color:C.blue}}> En route</span>}
                            {t.status==="AVAILABLE"&&<span style={{fontSize:9.5,color:C.green}}> Available</span>}
                            {t.status==="LOADING"&&<span style={{fontSize:9.5,color:C.amber}}>Loading</span>}
                            {t.status==="DELIVERING"&&<span style={{fontSize:9.5,color:C.green}}> Delivering</span>}
                          </div>
                        </div>
                      );
                    })}
                  </div>
                ))}
              </div>

              {/* Carrier compliance scorecard */}
              <div style={{flex:"0 0 360px",display:"flex",flexDirection:"column",gap:12}}>

                <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                  <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}> Carrier Compliance Scorecard</div>
                  {CARRIER_FLEET.map(c=>{
                    const insExpiring = c.insuranceExpiry.includes("2025")&&!c.insuranceExpiry.includes("Dec");
                    const contractExpiring = c.contractExpiry.includes("2025");
                    const noVapor = !c.vaporRecovery;
                    const flags = [
                      insExpiring&&{msg:`Insurance renews ${c.insuranceExpiry}`,sev:"warn"},
                      contractExpiring&&{msg:`Contract expires ${c.contractExpiry}`,sev:"warn"},
                      noVapor&&{msg:"No vapor recovery — limits terminal access",sev:"info"},
                    ].filter(Boolean);
                    const score = 100 - flags.length*12 - (c.ytdOverShort<-50?15:0) - (c.ytdDetentionHrs>20?10:0);
                    return (
                      <div key={c.id} style={{padding:"10px 12px",borderRadius:8,marginBottom:6,border:`1px solid ${flags.length>0?C.amber:C.cardBord}`,background:darkMode?"rgba(255,255,255,.02)":"#F9FAFB"}}>
                        <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:flags.length>0?6:0}}>
                          <div>
                            <span style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{c.short} — {c.name}</span>
                            <span style={{marginLeft:8,fontSize:10,color:C.textSec}}>DOT: {c.dot}</span>
                          </div>
                          <div style={{display:"flex",alignItems:"center",gap:8}}>
                            <span style={{fontSize:9.5,color:C.textMut}}>Compliance</span>
                            <span style={{fontSize:14,fontWeight:900,color:score>=90?C.green:score>=75?C.amber:C.red,fontFamily:FONT}}>{score}</span>
                          </div>
                        </div>
                        {flags.map((f,fi)=>(
                          <div key={fi} style={{fontSize:10,color:f.sev==="warn"?C.amber:C.blue,marginTop:3}}>
                            {f.sev==="warn"?"":"ℹ"} {f.msg}
                          </div>
                        ))}
                      </div>
                    );
                  })}
                </div>

                {/* Reg quick ref */}
                <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                  <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:10}}> Regulatory Quick Reference</div>
                  {[
                    {cat:"FMCSA",  rule:"49 CFR 395 — HOS: 11-hr drive / 14-hr window / 30-min break after 8 hrs"},
                    {cat:"FMCSA",  rule:"49 CFR 396 — Inspections: annual + pre/post-trip required"},
                    {cat:"HazMat", rule:"49 CFR 172 — Placard required: FLAMMABLE LIQUID (UN 1203/1863/1202)"},
                    {cat:"EPA",    rule:"40 CFR 63 Subpart CCCCCC — Stage II vapor recovery at retail sites"},
                    {cat:"DOT",    rule:"Motor carrier registration + $750K minimum liability insurance"},
                    {cat:"IFTA",   rule:"Quarterly fuel tax filing — due Apr 30, Jul 31, Oct 31, Jan 31"},
                    {cat:"State",  rule:"NC, SC, VA, GA, FL all require intrastate motor carrier permit"},
                  ].map((r,ri)=>(
                    <div key={ri} style={{padding:"6px 0",borderBottom:`1px solid ${C.cardBord}`,display:"flex",gap:8}}>
                      <span style={{fontSize:9,fontWeight:700,padding:"2px 6px",borderRadius:5,background:darkMode?"rgba(59,130,246,.1)":"#EFF6FF",color:C.blue,flexShrink:0,height:"fit-content",marginTop:1}}>{r.cat}</span>
                      <span style={{fontSize:10,color:C.textSec,lineHeight:1.4}}>{r.rule}</span>
                    </div>
                  ))}
                </div>

              </div>
            </div>
          </div>
        )}

      </div>
    );
  };

  //  Tab: Strategy 
  const renderStrategy = () => {
    const FONT = "Arial,sans-serif";
    // Disruption impact calc
    const offlineTerminals = [disruptionTerminal];
    const affectedStores = STORES.filter(s=>offlineTerminals.includes(s.terminal));
    const safeStores = STORES.filter(s=>!offlineTerminals.includes(s.terminal));
    const daysOut = disruptionDays;
    const affectedVol = affectedStores.reduce((a,s)=>a+s.totalDailyVol*daysOut,0);
    // Rerouting cost premium (alt supply costs more)
    const reroutePremium = 0.035; // ~3.5¢ more via alt supply
    const rerouteCost = affectedVol * reroutePremium;
    const criticalByDay2 = affectedStores.filter(s=>GRADES.some(g=>s.daysSupply[g]<daysOut)).length;
    const exposureDollar = UNHEDGED * AVG_LANDED;
    const exposureAt5c  = UNHEDGED * 0.05;
    const exposureAt10c = UNHEDGED * 0.10;
    const exposureAt20c = UNHEDGED * 0.20;

    // ─── Contract portfolio position from TERMINAL_SUPPLIERS ──────────────
    // Real current mix by commit volume + MTD spot lifts: primary / secondary
    // / spot-only. Becomes the ground-truth baseline for the mix simulator
    // (rather than the hardcoded 78% we used before the suppliers layer).
    const contractSuppliers = TERMINAL_SUPPLIERS.filter(s => s.contractStatus !== "spot-only");
    const spotSuppliersForPortfolio = TERMINAL_SUPPLIERS.filter(s => s.contractStatus === "spot-only");
    const primaryCommit = contractSuppliers
      .filter(s => s.contractStatus === "primary")
      .reduce((a,s) => a + s.monthlyCommit, 0);
    const secondaryCommit = contractSuppliers
      .filter(s => s.contractStatus === "secondary")
      .reduce((a,s) => a + s.monthlyCommit, 0);
    const totalContractCommit = primaryCommit + secondaryCommit;
    const spotMTD = spotSuppliersForPortfolio.reduce((a,s) => a + (s.liftedMTD || 0), 0);
    // Project monthly spot volume (we're 22/30 through month)
    const projSpotMonthly = spotMTD / 22 * 30;
    const projTotalMonthly = totalContractCommit + projSpotMonthly;
    const primaryShare = projTotalMonthly > 0 ? primaryCommit / projTotalMonthly : 0;
    const secondaryShare = projTotalMonthly > 0 ? secondaryCommit / projTotalMonthly : 0;
    const spotShare = projTotalMonthly > 0 ? projSpotMonthly / projTotalMonthly : 0;
    const currentContractSharePct = Math.round((primaryShare + secondaryShare) * 100);
    const positionIsBalanced = currentContractSharePct >= 75 && currentContractSharePct <= 88;

    // ─── Contract vs Spot decision data ───────────────────────────────────
    // Forward curve — pick the relevant product per grade
    const curvePrices = strategyGrade === "Diesel" ? FORWARD_CURVE.ulsd : FORWARD_CURVE.rbob;
    const curveProduct = strategyGrade === "Diesel" ? "ULSD" : "RBOB";
    const slope3mo = curveSlope(curvePrices, 3);
    const slope6mo = curveSlope(curvePrices, 6);
    const curveMin = Math.min(...curvePrices);
    const curveMax = Math.max(...curvePrices);
    const curvePadY = (curveMax - curveMin) * 0.15 || 0.02;

    // Lift-ahead optimizer — given current curve shape, compute expected
    // savings from carrying extra inventory vs normal pace. Simple model:
    //   • Normal pace: lift the quantity you'd naturally consume, no extra carrying.
    //   • Lift-ahead: carry `liftAheadDays` of inventory at today's price.
    //   • If forward curve is in contango, that inventory will be worth more
    //     than the replacement cost at normal pace, so you win.
    //   • Subtract storage/carrying cost of ~$0.0015/gal/day (industry typical).
    // The totals are portfolio-level: daily gasoline volume × days × delta.
    const TOTAL_DAILY_GAL = STORES.reduce((a,s)=>a+s.totalDailyVol,0);
    const STORAGE_COST_PER_GAL_PER_DAY = 0.0015;
    const todayPrice = curvePrices[0];
    // Price at the "replacement" point — where the deferred lift would land
    // on the curve if you carry `liftAheadDays`. Linear interpolation within
    // the first month (0-30 days) for honesty.
    const replacementMonths = liftAheadDays / 30;
    const replacementPrice = todayPrice + (curvePrices[1] - curvePrices[0]) * replacementMonths;
    const priceGain = replacementPrice - todayPrice; // $/gal captured by lifting now
    const carryCost = STORAGE_COST_PER_GAL_PER_DAY * liftAheadDays; // $/gal cost
    const netGainPerGal = priceGain - carryCost;
    const extraVolume = TOTAL_DAILY_GAL * liftAheadDays;
    const netGainTotal = netGainPerGal * extraVolume;
    const liftRecommendation = netGainPerGal > 0.003 ? "LIFT AHEAD"
                              : netGainPerGal < -0.003 ? "DEFER"
                              : "HOLD PACE";

    // Contract mix simulator — compare scenarios. Historical average spot
    // price is ~$0.012/gal below contract rack today (varies); we use that
    // as the baseline advantage of spot. Risk premium for spot is the
    // historical volatility surcharge during allocation/hurricane events,
    // which we estimate at $0.025/gal on the spot portion (empirical
    // wisdom: spot costs spike 1-2x per year).
    const SPOT_DISCOUNT_VS_CONTRACT = 0.0087;  // $/gal spot cheaper than contract in stable market
    const SPOT_RISK_PREMIUM_ANNUAL = 0.025;    // $/gal expected extra cost during ~2 disruption events/yr (weighted)
    const ANNUAL_VOL = TOTAL_DAILY_GAL * 365;
    const currentContractPct = currentContractSharePct; // baseline from TERMINAL_SUPPLIERS data (was hardcoded 78)
    const simContractShare = mixSimContract / 100;
    const simSpotShare = 1 - simContractShare;
    const baselineContractShare = currentContractPct / 100;
    const baselineSpotShare = 1 - baselineContractShare;
    // Scenario annual cost delta vs baseline
    const scenarioSpotAdvantage = simSpotShare * ANNUAL_VOL * SPOT_DISCOUNT_VS_CONTRACT;
    const scenarioSpotRisk      = simSpotShare * ANNUAL_VOL * SPOT_RISK_PREMIUM_ANNUAL;
    const scenarioNet = scenarioSpotAdvantage - scenarioSpotRisk;
    const baselineSpotAdvantage = baselineSpotShare * ANNUAL_VOL * SPOT_DISCOUNT_VS_CONTRACT;
    const baselineSpotRisk      = baselineSpotShare * ANNUAL_VOL * SPOT_RISK_PREMIUM_ANNUAL;
    const baselineNet = baselineSpotAdvantage - baselineSpotRisk;
    const scenarioVsBaseline = scenarioNet - baselineNet;

    return (
      <div style={{display:"flex",flexDirection:"column",gap:14}}>

        {/* ═══ CONTRACT vs SPOT DECISION TOOLS ═══════════════════════════ */}

        {/* Section 0: Contract portfolio position — real data from TERMINAL_SUPPLIERS */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16}}>
          <div style={{marginBottom:12}}>
            <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
              Contract portfolio position
            </div>
            <div style={{fontSize:10.5, color:C.textSec, marginTop:2, fontFamily:FONT}}>
              Your actual contract mix across all suppliers — the ground-truth baseline the decisions below are measured against
            </div>
          </div>

          {/* Stacked bar showing the mix */}
          <div style={{marginBottom:14}}>
            <div style={{display:"flex", height:40, borderRadius:7, overflow:"hidden", border:`1px solid ${C.cardBord}`}}>
              <div title={`Primary contracts: ${(primaryCommit/1_000_000).toFixed(1)}M gal/month`}
                style={{
                  width:`${primaryShare*100}%`,
                  background:"#16A34A",
                  display:"flex", alignItems:"center", justifyContent:"center",
                  color:"#fff", fontSize:11, fontWeight:800, fontFamily:FONT,
                }}>
                {primaryShare > 0.08 ? `PRIMARY ${Math.round(primaryShare*100)}%` : ""}
              </div>
              <div title={`Secondary contracts: ${(secondaryCommit/1_000_000).toFixed(1)}M gal/month`}
                style={{
                  width:`${secondaryShare*100}%`,
                  background:"#F4D398",
                  display:"flex", alignItems:"center", justifyContent:"center",
                  color:"#fff", fontSize:11, fontWeight:800, fontFamily:FONT,
                }}>
                {secondaryShare > 0.08 ? `SECONDARY ${Math.round(secondaryShare*100)}%` : ""}
              </div>
              <div title={`Spot: ${(projSpotMonthly/1_000_000).toFixed(1)}M gal/month projected`}
                style={{
                  width:`${spotShare*100}%`,
                  background:"#EA580C",
                  display:"flex", alignItems:"center", justifyContent:"center",
                  color:"#fff", fontSize:11, fontWeight:800, fontFamily:FONT,
                }}>
                {spotShare > 0.06 ? `SPOT ${Math.round(spotShare*100)}%` : ""}
              </div>
            </div>
            <div style={{display:"flex", justifyContent:"space-between", marginTop:6, fontSize:10, color:C.textMut, fontFamily:FONT}}>
              <span>0%</span>
              <span>Total monthly projected: {(projTotalMonthly/1_000_000).toFixed(1)}M gal</span>
              <span>100%</span>
            </div>
          </div>

          {/* Three-stat breakdown */}
          <div style={{display:"grid", gridTemplateColumns:"repeat(3, 1fr)", gap:10}}>
            {[
              {
                label:"Primary contracts",
                val:`${(primaryCommit/1_000_000).toFixed(1)}M`,
                sub:`${contractSuppliers.filter(s=>s.contractStatus==="primary").length} suppliers · guaranteed allocation`,
                color:"#16A34A",
              },
              {
                label:"Secondary contracts",
                val:`${(secondaryCommit/1_000_000).toFixed(1)}M`,
                sub:`${contractSuppliers.filter(s=>s.contractStatus==="secondary").length} suppliers · competitive backup`,
                color:"#F4D398",
              },
              {
                label:"Spot (projected)",
                val:`${(projSpotMonthly/1_000_000).toFixed(1)}M`,
                sub:`${spotSuppliersForPortfolio.length} suppliers · no commitment · allocation risk`,
                color:"#EA580C",
              },
            ].map((k,ki) => (
              <div key={ki} style={{
                padding:"10px 12px", borderRadius:7,
                background: darkMode?"rgba(255,255,255,.02)":"#FAFBFD",
                border:`1px solid ${k.color}30`,
              }}>
                <div style={{fontSize:9, fontWeight:800, color:k.color, letterSpacing:.5, textTransform:"uppercase"}}>
                  {k.label}
                </div>
                <div style={{fontSize:18, fontWeight:900, color:C.textPri, fontFamily:"Arial,sans-serif", lineHeight:1.1, marginTop:4}}>
                  {k.val}
                  <span style={{fontSize:10, color:C.textMut, marginLeft:4, fontWeight:500}}>gal/mo</span>
                </div>
                <div style={{fontSize:10, color:C.textSec, marginTop:4, fontFamily:FONT}}>
                  {k.sub}
                </div>
              </div>
            ))}
          </div>

          {/* Plain-English assessment */}
          <div style={{
            marginTop:12, padding:"10px 14px", borderRadius:7,
            background: positionIsBalanced
              ? (darkMode?"rgba(22,163,74,.06)":"#F0FDF4")
              : (darkMode?"rgba(245,158,11,.06)":"#F8FAFB"),
            border:`1px solid ${positionIsBalanced ? "rgba(22,163,74,.3)" : "rgba(245,158,11,.3)"}`,
          }}>
            <div style={{fontSize:10.5, color:C.textSec, fontFamily:FONT, lineHeight:1.5}}>
              <strong style={{color: positionIsBalanced ? "#16A34A" : "#B45309"}}>
                {positionIsBalanced ? "Position is balanced" : "Position may warrant review"}
              </strong>
              {" — "}
              You're {currentContractSharePct}% contracted / {100-currentContractSharePct}% spot. Industry typical for SE US c-store chains is 75-88% contract, balancing supply reliability against spot arbitrage.
              {currentContractSharePct < 75 && " Under-contracted position carries allocation risk during disruption events (hurricanes, refinery outages)."}
              {currentContractSharePct > 88 && " Over-contracted position foregoes spot arbitrage opportunities in stable markets."}
              {" The simulator below lets you model shifting this mix by ±5-15 percentage points to see the annual P&L impact."}
            </div>
          </div>
        </div>

        {/* Section 1: Forward curve */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16}}>
          <div style={{display:"flex", alignItems:"center", justifyContent:"space-between", marginBottom:10, flexWrap:"wrap", gap:8}}>
            <div>
              <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
                NYMEX forward curve — {curveProduct} futures
              </div>
              <div style={{fontSize:10.5, color:C.textSec, marginTop:2, fontFamily:FONT}}>
                The futures strip procurement uses to decide lift timing and contract mix
              </div>
            </div>
            <div style={{display:"flex", gap:6}}>
              {["Regular","Premium","Diesel"].map(g => (
                <button key={g} onClick={()=>setStrategyGrade(g)}
                  style={{
                    padding:"5px 11px", borderRadius:6,
                    border:`1px solid ${strategyGrade===g?C.gold:C.cardBord}`,
                    background: strategyGrade===g ? (darkMode?"rgba(200,164,74,.12)":"#FFF9E6") : "transparent",
                    color: strategyGrade===g ? C.gold : C.textSec,
                    fontSize:10.5, fontWeight: strategyGrade===g?700:500,
                    cursor:"pointer", fontFamily:FONT,
                  }}>{g}</button>
              ))}
            </div>
          </div>

          {/* Shape callout pill */}
          <div style={{display:"flex", gap:8, marginBottom:12, flexWrap:"wrap"}}>
            <div style={{
              padding:"8px 14px", borderRadius:8,
              background: slope3mo.shape === "contango" ? (darkMode?"rgba(245,158,11,.10)":"#F8FAFB")
                        : slope3mo.shape === "backwardation" ? (darkMode?"rgba(22,163,74,.10)":"#F0FDF4")
                        : (darkMode?"rgba(255,255,255,.03)":"#FAFBFD"),
              border:`1px solid ${slope3mo.shape === "contango" ? "rgba(245,158,11,.4)" : slope3mo.shape === "backwardation" ? "rgba(22,163,74,.4)" : C.cardBord}`,
              flex:1, minWidth:260,
            }}>
              <div style={{fontSize:9.5, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:3}}>
                3-month shape
              </div>
              <div style={{fontSize:14, fontWeight:800, color: slope3mo.shape === "contango" ? "#D97706" : slope3mo.shape === "backwardation" ? "#16A34A" : C.textPri, fontFamily:FONT, textTransform:"capitalize"}}>
                {slope3mo.shape === "contango" ? "Contango" : slope3mo.shape === "backwardation" ? "Backwardation" : "Flat"}
                <span style={{fontSize:11, color:C.textSec, fontWeight:600, marginLeft:8}}>
                  ({slope3mo.spread > 0 ? "+" : ""}${slope3mo.spread.toFixed(4)}/gal over 3mo)
                </span>
              </div>
              <div style={{fontSize:10, color:C.textSec, marginTop:4, lineHeight:1.4, fontFamily:FONT}}>
                {slope3mo.shape === "contango"
                  ? "Prices rising → lift now, contract more of annual volume."
                  : slope3mo.shape === "backwardation"
                  ? "Prices falling → defer lifts where possible, increase spot share."
                  : "Stable market → neutral lift timing, maintain current mix."}
              </div>
            </div>
            <div style={{
              padding:"8px 14px", borderRadius:8,
              background: darkMode?"rgba(255,255,255,.03)":"#FAFBFD",
              border:`1px solid ${C.cardBord}`,
              flex:1, minWidth:260,
            }}>
              <div style={{fontSize:9.5, fontWeight:800, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:3}}>
                6-month shape
              </div>
              <div style={{fontSize:14, fontWeight:800, color:C.textPri, fontFamily:FONT, textTransform:"capitalize"}}>
                {slope6mo.shape}
                <span style={{fontSize:11, color:C.textSec, fontWeight:600, marginLeft:8}}>
                  ({slope6mo.spread > 0 ? "+" : ""}${slope6mo.spread.toFixed(4)}/gal)
                </span>
              </div>
              <div style={{fontSize:10, color:C.textSec, marginTop:4, lineHeight:1.4, fontFamily:FONT}}>
                Slope = ${slope6mo.perMonth.toFixed(4)}/gal per month. Use this for annual contract negotiation framing.
              </div>
            </div>
          </div>

          {/* Forward curve chart — SVG keeps 720:120 (6:1) aspect, scales with container width */}
          <div style={{position:"relative", background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD", borderRadius:8, padding:"16px 14px 24px 14px", border:`1px solid ${C.cardBord}`}}>
            <svg width="100%" viewBox="0 0 720 120" preserveAspectRatio="xMidYMid meet" style={{display:"block"}}>
              {/* Grid lines */}
              {[0, 0.25, 0.5, 0.75, 1].map((f, fi) => (
                <line key={fi} x1="40" y1={10 + f*100} x2="720" y2={10 + f*100}
                  stroke={darkMode?"#1E2840":"#E2E8F0"} strokeWidth="0.5" strokeDasharray={fi===0||fi===4?"":"2,2"}/>
              ))}
              {/* Y-axis labels */}
              {[0, 0.5, 1].map((f, fi) => {
                const price = curveMax + curvePadY - f*((curveMax-curveMin)+2*curvePadY);
                return (
                  <text key={fi} x="36" y={14+f*100} textAnchor="end" fontSize="8" fill={darkMode?"#7B8FAF":"#4A5E7A"} fontFamily="Arial,sans-serif">
                    ${price.toFixed(3)}
                  </text>
                );
              })}
              {/* Curve line */}
              {(() => {
                const points = curvePrices.map((p, i) => {
                  const x = 40 + (i/(curvePrices.length-1)) * 680;
                  const y = 10 + ((curveMax + curvePadY - p) / ((curveMax-curveMin) + 2*curvePadY)) * 100;
                  return { x, y };
                });
                const pathD = points.map((p, i) => `${i===0?"M":"L"} ${p.x},${p.y}`).join(" ");
                return (
                  <>
                    {/* Shaded area under curve */}
                    <path d={`${pathD} L 720,110 L 40,110 Z`} fill={slope3mo.shape === "contango" ? "rgba(217,119,6,.08)" : slope3mo.shape === "backwardation" ? "rgba(22,163,74,.08)" : "rgba(100,116,139,.08)"} />
                    {/* The curve */}
                    <path d={pathD} fill="none" stroke={slope3mo.shape === "contango" ? "#D97706" : slope3mo.shape === "backwardation" ? "#16A34A" : "#64748B"} strokeWidth="2.5" strokeLinejoin="round" strokeLinecap="round"/>
                    {/* Points */}
                    {points.map((p, i) => (
                      <g key={i}>
                        <circle cx={p.x} cy={p.y} r={i===0?4:3} fill={i===0 ? "#F4D398" : (slope3mo.shape === "contango" ? "#D97706" : slope3mo.shape === "backwardation" ? "#16A34A" : "#64748B")} stroke={darkMode?"#13182A":"#fff"} strokeWidth="1.5"/>
                        {i===0 && (
                          <text x={p.x} y={p.y-9} textAnchor="middle" fontSize="8" fontWeight="800" fill={C.gold} fontFamily="Arial,sans-serif">TODAY</text>
                        )}
                        {(i%2===0 || i===curvePrices.length-1) && (
                          <text x={p.x} y="118" textAnchor="middle" fontSize="8" fill={darkMode?"#7B8FAF":"#4A5E7A"} fontFamily="Arial,sans-serif">{FORWARD_CURVE.months[i]}</text>
                        )}
                      </g>
                    ))}
                  </>
                );
              })()}
            </svg>
          </div>

          <div style={{fontSize:9.5, color:C.textMut, marginTop:8, fontStyle:"italic", fontFamily:FONT}}>
            Curve data simulated for demo. Production integration: CME direct feed or Refinitiv/Bloomberg for live NYMEX {curveProduct} futures.
          </div>
        </div>

        {/* Section 2: Lift-ahead optimizer */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16}}>
          <div style={{marginBottom:12}}>
            <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
              Lift-ahead optimizer
            </div>
            <div style={{fontSize:10.5, color:C.textSec, marginTop:2, fontFamily:FONT}}>
              Given the forward curve, should we pull forward lifts to capture price movement?
            </div>
          </div>

          <div style={{display:"grid", gridTemplateColumns:"1fr 1fr", gap:14}}>
            {/* Input controls */}
            <div>
              <div style={{fontSize:10.5, fontWeight:700, color:C.textSec, marginBottom:8, fontFamily:FONT}}>
                Extra inventory days to carry
              </div>
              <div style={{display:"flex", gap:10, alignItems:"center"}}>
                <input type="range" min="0" max="14" step="1" value={liftAheadDays}
                  onChange={e=>setLiftAheadDays(+e.target.value)}
                  style={{flex:1, accentColor:C.gold}}
                />
                <div style={{width:60, textAlign:"center", padding:"6px 10px", background:darkMode?"rgba(200,164,74,.12)":"#FFF9E6", borderRadius:6, border:`1px solid ${C.gold}40`}}>
                  <span style={{fontSize:16, fontWeight:800, color:C.gold, fontFamily:FONT}}>{liftAheadDays}</span>
                  <span style={{fontSize:9, color:C.textMut, marginLeft:3}}>days</span>
                </div>
              </div>
              <div style={{fontSize:9.5, color:C.textMut, marginTop:4, fontFamily:FONT}}>
                0 = normal pace · 7 = one week extra · 14 = two weeks extra (near tank capacity)
              </div>

              <div style={{marginTop:18, padding:"12px 14px", borderRadius:8, background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD", border:`1px solid ${C.cardBord}`, fontFamily:FONT}}>
                <div style={{fontSize:10, fontWeight:700, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:6}}>
                  Math breakdown
                </div>
                <div style={{fontSize:10.5, color:C.textSec, lineHeight:1.9}}>
                  <div style={{display:"flex", justifyContent:"space-between"}}>
                    <span>Extra volume to buy:</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:600, color:C.textPri}}>{(extraVolume/1000).toFixed(0)}K gal</span>
                  </div>
                  <div style={{display:"flex", justifyContent:"space-between"}}>
                    <span>Price captured (curve):</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:600, color: priceGain > 0 ? "#16A34A" : "#DC2626"}}>
                      {priceGain > 0 ? "+" : ""}${priceGain.toFixed(4)}/gal
                    </span>
                  </div>
                  <div style={{display:"flex", justifyContent:"space-between"}}>
                    <span>Storage/carry cost:</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:600, color:"#DC2626"}}>
                      −${carryCost.toFixed(4)}/gal
                    </span>
                  </div>
                  <div style={{display:"flex", justifyContent:"space-between", borderTop:`1px solid ${C.cardBord}`, paddingTop:4, marginTop:4}}>
                    <span style={{fontWeight:700}}>Net per gal:</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:800, color: netGainPerGal > 0 ? "#16A34A" : "#DC2626"}}>
                      {netGainPerGal > 0 ? "+" : ""}${netGainPerGal.toFixed(4)}
                    </span>
                  </div>
                </div>
              </div>
            </div>

            {/* Recommendation */}
            <div style={{
              padding:"18px 20px", borderRadius:10,
              background: liftRecommendation === "LIFT AHEAD" ? (darkMode?"rgba(22,163,74,.08)":"#F0FDF4")
                        : liftRecommendation === "DEFER" ? (darkMode?"rgba(234,88,12,.08)":"#FFF7ED")
                        : (darkMode?"rgba(255,255,255,.03)":"#FAFBFD"),
              border:`2px solid ${liftRecommendation === "LIFT AHEAD" ? "#16A34A" : liftRecommendation === "DEFER" ? "#EA580C" : C.cardBord}`,
              textAlign:"center",
            }}>
              <div style={{fontSize:10, fontWeight:800, color:C.textMut, letterSpacing:.8, textTransform:"uppercase", marginBottom:8}}>
                Recommendation
              </div>
              <div style={{fontSize:26, fontWeight:900, color: liftRecommendation === "LIFT AHEAD" ? "#16A34A" : liftRecommendation === "DEFER" ? "#EA580C" : C.textPri, fontFamily:FONT, letterSpacing:.5, marginBottom:6}}>
                {liftRecommendation}
              </div>
              <div style={{fontSize:18, fontWeight:800, color:C.textPri, fontFamily:FONT, marginBottom:4}}>
                {netGainTotal > 0 ? "+" : ""}${Math.round(Math.abs(netGainTotal)).toLocaleString()}
              </div>
              <div style={{fontSize:10, color:C.textSec, fontFamily:FONT}}>
                {netGainTotal > 0 ? "captured" : "foregone"} over next {liftAheadDays || 1} day{liftAheadDays===1?"":"s"}
              </div>
              <div style={{fontSize:10, color:C.textMut, marginTop:10, lineHeight:1.5, fontFamily:FONT}}>
                {liftRecommendation === "LIFT AHEAD"
                  ? "Forward curve is in contango — today's price is cheap relative to what we'd pay waiting. Capture the spread."
                  : liftRecommendation === "DEFER"
                  ? "Backwardation — waiting saves money. Storage cost is the only reason not to defer further."
                  : "Net gain below operational threshold. Carry cost offsets the curve spread. Hold normal pace."}
              </div>
            </div>
          </div>
        </div>

        {/* Section 3: Contract mix simulator */}
        <div style={{background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16}}>
          <div style={{marginBottom:12}}>
            <div style={{fontSize:12, fontWeight:800, color:C.textPri, fontFamily:FONT}}>
              Contract vs spot mix simulator
            </div>
            <div style={{fontSize:10.5, color:C.textSec, marginTop:2, fontFamily:FONT}}>
              Annual structure decision — what if we'd contracted more or less of last year's volume?
            </div>
          </div>

          <div style={{display:"grid", gridTemplateColumns:"1fr 1fr", gap:14, alignItems:"start"}}>
            {/* Slider + breakdown */}
            <div>
              <div style={{fontSize:10.5, fontWeight:700, color:C.textSec, marginBottom:6, fontFamily:FONT}}>
                Contract share (current: {currentContractPct}%)
              </div>
              <input type="range" min="50" max="95" step="1" value={mixSimContract}
                onChange={e=>setMixSimContract(+e.target.value)}
                style={{width:"100%", accentColor:C.gold}}
              />
              {/* Visual split bar */}
              <div style={{position:"relative", height:36, borderRadius:7, overflow:"hidden", marginTop:10, background:darkMode?"rgba(255,255,255,.04)":"#F0F3F8", border:`1px solid ${C.cardBord}`}}>
                <div style={{position:"absolute", left:0, top:0, bottom:0, width:`${mixSimContract}%`, background:"linear-gradient(90deg, #16A34A, #22C55E)", display:"flex", alignItems:"center", paddingLeft:10, color:"#fff", fontWeight:800, fontSize:11, fontFamily:FONT}}>
                  Contract {mixSimContract}%
                </div>
                <div style={{position:"absolute", right:0, top:0, bottom:0, width:`${100-mixSimContract}%`, background:"linear-gradient(90deg, #EA580C, #F59E0B)", display:"flex", alignItems:"center", justifyContent:"flex-end", paddingRight:10, color:"#fff", fontWeight:800, fontSize:11, fontFamily:FONT}}>
                  Spot {100-mixSimContract}%
                </div>
                {/* Marker at current */}
                <div style={{position:"absolute", left:`${currentContractPct}%`, top:-4, bottom:-4, width:2, background:C.gold, transform:"translateX(-1px)"}}/>
              </div>
              <div style={{fontSize:9, color:C.textMut, marginTop:4, fontFamily:FONT}}>
                Gold marker = current mix
              </div>

              <div style={{marginTop:18, padding:"12px 14px", borderRadius:8, background:darkMode?"rgba(255,255,255,.02)":"#FAFBFD", border:`1px solid ${C.cardBord}`, fontFamily:FONT}}>
                <div style={{fontSize:10, fontWeight:700, color:C.textMut, letterSpacing:.5, textTransform:"uppercase", marginBottom:6}}>
                  Annual P&L math (based on {(ANNUAL_VOL/1_000_000).toFixed(0)}M gal volume)
                </div>
                <div style={{fontSize:10.5, color:C.textSec, lineHeight:1.9}}>
                  <div style={{display:"flex", justifyContent:"space-between"}}>
                    <span>Spot share savings vs contract:</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:600, color:"#16A34A"}}>
                      +${Math.round(scenarioSpotAdvantage).toLocaleString()}
                    </span>
                  </div>
                  <div style={{display:"flex", justifyContent:"space-between"}}>
                    <span>Expected disruption cost (2 events/yr):</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:600, color:"#DC2626"}}>
                      −${Math.round(scenarioSpotRisk).toLocaleString()}
                    </span>
                  </div>
                  <div style={{display:"flex", justifyContent:"space-between", borderTop:`1px solid ${C.cardBord}`, paddingTop:4, marginTop:4}}>
                    <span style={{fontWeight:700}}>Net vs full-contract:</span>
                    <span style={{fontFamily:"Arial,sans-serif", fontWeight:800, color: scenarioNet > 0 ? "#16A34A" : "#DC2626"}}>
                      {scenarioNet > 0 ? "+" : ""}${Math.round(scenarioNet).toLocaleString()}
                    </span>
                  </div>
                </div>
              </div>
            </div>

            {/* Scenario comparison */}
            <div style={{
              padding:"16px 18px", borderRadius:10,
              background: scenarioVsBaseline > 0 ? (darkMode?"rgba(22,163,74,.08)":"#F0FDF4") : scenarioVsBaseline < 0 ? (darkMode?"rgba(234,88,12,.08)":"#FFF7ED") : (darkMode?"rgba(255,255,255,.03)":"#FAFBFD"),
              border:`2px solid ${scenarioVsBaseline > 0 ? "#16A34A" : scenarioVsBaseline < 0 ? "#EA580C" : C.cardBord}`,
              textAlign:"center",
            }}>
              <div style={{fontSize:10, fontWeight:800, color:C.textMut, letterSpacing:.8, textTransform:"uppercase", marginBottom:8}}>
                Scenario vs baseline ({currentContractPct}/{100-currentContractPct})
              </div>
              <div style={{fontSize:28, fontWeight:900, color: scenarioVsBaseline > 0 ? "#16A34A" : scenarioVsBaseline < 0 ? "#EA580C" : C.textPri, fontFamily:FONT, marginBottom:6}}>
                {scenarioVsBaseline > 0 ? "+" : ""}${Math.round(scenarioVsBaseline).toLocaleString()}
              </div>
              <div style={{fontSize:11, color:C.textSec, fontFamily:FONT, marginBottom:14}}>
                annual {scenarioVsBaseline > 0 ? "gain" : "cost"} vs today's mix
              </div>
              <div style={{fontSize:10, color:C.textMut, lineHeight:1.5, fontFamily:FONT, paddingTop:10, borderTop:`1px solid ${C.cardBord}`}}>
                {mixSimContract > currentContractPct
                  ? "Shifting more to contract reduces disruption risk but forgoes spot arbitrage. Good for volatile supply environments."
                  : mixSimContract < currentContractPct
                  ? "Shifting more to spot captures price dips but raises exposure during allocation events and hurricane season."
                  : "This is your current mix. Adjust the slider to see alternative structures."}
              </div>
            </div>
          </div>

          <div style={{fontSize:9.5, color:C.textMut, marginTop:14, fontStyle:"italic", fontFamily:FONT}}>
            Model assumptions: spot averages $0.0087/gal cheaper than contract in stable markets, but spikes +$0.025/gal during ~2 disruption events per year (weighted across annual volume). Actual results depend on contract terms, terminal mix, and hedge coverage. Stress-test with the disruption scenarios below.
          </div>
        </div>

        {/* ═══ EXISTING EXPOSURE & DISRUPTION TOOLS ═══════════════════════ */}
        <div style={{display:"flex",gap:14}}>

          {/* Exposure dashboard */}
          <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
            <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Price Exposure Dashboard</div>
            <div style={{fontSize:10.5,color:C.textSec,marginBottom:14}}>Total monthly purchase exposure and hedge coverage</div>

            {/* Hedge donut */}
            <div style={{display:"flex",gap:16,alignItems:"center",marginBottom:16}}>
              <Donut slices={[{v:HEDGED_VOL,color:C.green},{v:UNHEDGED,color:C.amber}]} size={72} thick={10} C={C}/>
              <div>
                <div style={{fontSize:22,fontWeight:900,color:C.textPri,fontFamily:FONT}}>{Math.round(HEDGED_VOL/MONTHLY_VOL*100)}%</div>
                <div style={{fontSize:10.5,color:C.textSec}}>hedged · {(HEDGED_VOL/1000).toFixed(0)}K gal/month</div>
                <div style={{fontSize:10.5,color:C.amber,marginTop:2}}>{Math.round(UNHEDGED/MONTHLY_VOL*100)}% unhedged · {(UNHEDGED/1000).toFixed(0)}K gal at risk</div>
              </div>
            </div>

            {/* Price move impact table */}
            <div style={{fontSize:10,fontWeight:700,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,fontFamily:FONT,marginBottom:8}}>Unhedged Exposure — Monthly P&L Impact</div>
            {[
              {move:"+$0.05",val:exposureAt5c,dir:1},
              {move:"+$0.10",val:exposureAt10c,dir:1},
              {move:"+$0.20",val:exposureAt20c,dir:1},
              {move:"-$0.05",val:exposureAt5c,dir:-1},
              {move:"-$0.10",val:exposureAt10c,dir:-1},
            ].map((row,i)=>(
              <div key={i} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"6px 10px",borderRadius:6,marginBottom:4,background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC"}}>
                <div style={{display:"flex",alignItems:"center",gap:8}}>
                  <div style={{width:32,height:5,borderRadius:2,background:row.dir>0?C.red:C.green}}/>
                  <span style={{fontSize:11,fontWeight:700,color:row.dir>0?C.red:C.green,fontFamily:FONT}}>Rack {row.move}/gal</span>
                </div>
                <span style={{fontSize:13,fontWeight:800,color:row.dir>0?C.red:C.green,fontFamily:FONT}}>
                  {row.dir>0?"+":"-"}${(row.val/1000).toFixed(0)}K to monthly cost
                </span>
              </div>
            ))}
            <div style={{marginTop:12,padding:"10px 12px",borderRadius:7,background:darkMode?"rgba(200,164,74,.1)":"#FFF9E6",border:`1px solid ${C.gold}30`}}>
              <div style={{fontSize:11,color:C.gold,fontWeight:700,fontFamily:FONT}}> Hedge Recommendation</div>
              <div style={{fontSize:10.5,color:C.textSec,marginTop:4}}>Target 55–65% hedge ratio on diesel. Current 38% leaves ${(exposureAt10c/1000).toFixed(0)}K exposure to a $0.10 move. Buy ULSD futures to cover forward 45-day diesel volume.</div>
            </div>
          </div>

          {/* Disruption Simulator */}
          <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
            <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Supply Disruption Simulator</div>
            <div style={{fontSize:10.5,color:C.textSec,marginBottom:14}}>Model the impact of a Colonial outage or terminal shutdown on your portfolio</div>

            <div style={{display:"flex",gap:12,marginBottom:14,flexWrap:"wrap"}}>
              <div style={{flex:1,minWidth:160}}>
                <div style={{fontSize:10,color:C.textSec,fontFamily:FONT,marginBottom:6}}>Terminal offline</div>
                <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
                  {TERMINALS.map(t=>(
                    <button key={t.id} onClick={()=>setDisruptionTerminal(t.id)}
                      style={{padding:"5px 10px",borderRadius:5,border:`1px solid ${disruptionTerminal===t.id?"#EF4444":C.cardBord}`,background:disruptionTerminal===t.id?"rgba(239,68,68,.12)":"transparent",color:disruptionTerminal===t.id?"#EF4444":C.textSec,fontSize:10.5,fontWeight:disruptionTerminal===t.id?700:400,cursor:"pointer",fontFamily:FONT,display:"flex",alignItems:"center",gap:4}}>
                      <ZoneBadge terminalId={t.id}/>{t.short}
                    </button>
                  ))}
                </div>
              </div>
              <div style={{flex:1,minWidth:140}}>
                <div style={{fontSize:10,color:C.textSec,fontFamily:FONT,marginBottom:6}}>Duration: {disruptionDays} days</div>
                <input type="range" min={1} max={14} value={disruptionDays} onChange={e=>setDisruptionDays(+e.target.value)}
                  style={{width:"100%",accentColor:"#EF4444"}}/>
                <div style={{display:"flex",justifyContent:"space-between"}}>
                  <span style={{fontSize:9.5,color:C.textMut}}>1 day</span>
                  <span style={{fontSize:9.5,color:C.textMut}}>14 days</span>
                </div>
              </div>
            </div>

            {/* Impact cards */}
            <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:10,marginBottom:14}}>
              {[
                {label:"Affected Stores",   val:affectedStores.length,   sub:`of ${STORES.length} total`,    color:"#EF4444"},
                {label:"Volume Displaced",  val:`${(affectedVol/1000).toFixed(0)}K gal`, sub:`${daysOut}-day outage`,      color:C.amber},
                {label:"Rerouting Cost",    val:`$${(rerouteCost/1000).toFixed(1)}K`,    sub:`at ${(reroutePremium*100).toFixed(1)}¢ premium`, color:C.amber},
                {label:"Sites Critical by Day 2", val:criticalByDay2, sub:"need emergency supply",           color:criticalByDay2>3?"#EF4444":C.amber},
              ].map((s,i)=>(
                <div key={i} style={{padding:"12px 14px",borderRadius:8,background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC",border:`1px solid ${C.cardBord}`}}>
                  <div style={{fontSize:9.5,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,fontFamily:FONT,marginBottom:4}}>{s.label}</div>
                  <div style={{fontSize:20,fontWeight:900,color:s.color,fontFamily:FONT}}>{s.val}</div>
                  <div style={{fontSize:10,color:C.textSec,marginTop:2}}>{s.sub}</div>
                </div>
              ))}
            </div>

            {/* Mitigation options */}
            <div style={{fontSize:10,fontWeight:700,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,fontFamily:FONT,marginBottom:8}}>Mitigation Options Available</div>
            {ALT_SUPPLY_POINTS.filter(s=>s.type!=="pipeline"||s.pipeline!=="Colonial").slice(0,4).map((sp,i)=>{
              const c = altLandedCost(sp,"Regular",STATE_TAX.NC);
              const canCover = affectedVol > 0;
              return (
                <div key={i} style={{display:"flex",alignItems:"center",gap:10,padding:"8px 10px",borderRadius:6,marginBottom:5,background:darkMode?"rgba(255,255,255,.025)":"#F9FAFB",border:`1px solid ${C.cardBord}`}}>
                  <span style={{fontSize:14}}>{ALT_SUPPLY_TYPES[sp.type]?.icon}</span>
                  <div style={{flex:1}}>
                    <div style={{fontSize:11,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{sp.name}</div>
                    <div style={{fontSize:10,color:C.textSec}}>Lead: {sp.leadDays}d · Grades: {sp.availableGrades.join(", ")}</div>
                  </div>
                  <div style={{textAlign:"right"}}>
                    {c&&<div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${c.spot.toFixed(4)}/gal</div>}
                    <div style={{fontSize:9.5,color:canCover?C.green:C.red,fontWeight:700}}>{canCover?"Can cover":"Insufficient"}</div>
                  </div>
                </div>
              );
            })}
          </div>
        </div>

        {/* Contract optimization */}
        <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
          <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:4}}> Contract Optimization — April Pace</div>
          <div style={{fontSize:10.5,color:C.textSec,marginBottom:14}}>Daily lift targets to hit minimums without over-committing. Running short = penalties. Running over = tied-up capital.</div>
          <div style={{display:"flex",gap:10,overflowX:"auto"}}>
            {TERMINALS.map((t,i)=>{
              const committed = 780000 + i*20000;
              const minVolume = Math.round(committed*0.92);
              // Stable seeded values — indexed so each terminal always shows the same pace
              const liftPcts  = [0.621, 0.584, 0.598, 0.641, 0.577, 0.609];
              const lifted    = Math.round(committed * liftPcts[i % liftPcts.length]);
              const daysLeft  = 16;
              const needed    = minVolume - lifted;
              const dailyNeed = needed / daysLeft;
              const pace      = lifted / (committed * (14/30));
              const onPace    = pace >= 0.92;
              const shortfall = needed > 0;
              const penaltyRisk = !onPace && needed > 50000;
              return (
                <div key={t.id} style={{flex:"0 0 200px",padding:"14px",borderRadius:10,border:`2px solid ${penaltyRisk?"#EF4444":onPace?C.green:C.cardBord}`,background:penaltyRisk?(darkMode?"rgba(239,68,68,.07)":"#FFF5F5"):darkMode?"rgba(255,255,255,.025)":"#F9FAFB"}}>
                  <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:6,display:"flex",alignItems:"center",gap:6}}><ZoneBadge terminalId={t.id}/>{t.short} — {t.name}</div>
                  <div style={{fontSize:20,fontWeight:900,color:onPace?C.green:C.amber,fontFamily:FONT}}>{Math.round(pace*100)}%</div>
                  <div style={{fontSize:10,color:C.textSec,marginBottom:8}}>of monthly pace target</div>
                  <InvBar pct={pace} color={onPace?C.green:C.amber} C={C}/>
                  <div style={{marginTop:8,display:"flex",flexDirection:"column",gap:4}}>
                    {[
                      {l:"Committed",v:`${(committed/1000).toFixed(0)}K gal`},
                      {l:"Lifted so far",v:`${(lifted/1000).toFixed(0)}K gal`},
                      {l:"Daily target",v:`${(dailyNeed/1000).toFixed(1)}K gal/day`},
                    ].map((row,ri)=>(
                      <div key={ri} style={{display:"flex",justifyContent:"space-between"}}>
                        <span style={{fontSize:9.5,color:C.textMut}}>{row.l}</span>
                        <span style={{fontSize:10,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{row.v}</span>
                      </div>
                    ))}
                  </div>
                  {penaltyRisk&&<div style={{marginTop:8,fontSize:9.5,color:"#EF4444",fontWeight:700,fontFamily:FONT}}> Penalty risk — increase daily lifts</div>}
                </div>
              );
            })}
          </div>
        </div>
      </div>
    );
  };

  //  Tab: Orders 
  const renderOrders = () => {
    const filtered = ORDERS.filter(o => {
      const matchSearch = !orderSearch || o.storeName.toLowerCase().includes(orderSearch.toLowerCase()) || o.id.includes(orderSearch);
      const matchFilter = orderFilter === "ALL" || o.status === orderFilter;
      return matchSearch && matchFilter;
    });

    return (
      <div style={{ display:"flex", flexDirection:"column", gap:14 }}>
        {/* Summary tiles */}
        <div style={{ display:"flex", gap:10 }}>
          {[
            { label:"Total Orders", val:ORDERS.length, color:C.textPri },
            { label:"In Transit", val:ORDERS.filter(o=>o.status==="En Route"||o.status==="At Terminal"||o.status==="Loaded").length, color:C.blue },
            { label:"Pending Dispatch", val:ORDERS.filter(o=>o.status==="Dispatched").length, color:C.amber },
            { label:"Delivered Today", val:ORDERS.filter(o=>o.status==="Delivered").length, color:C.green },
            { label:"Reconciled", val:ORDERS.filter(o=>o.status==="Reconciled").length, color:C.textSec },
          ].map((t,i)=>(
            <div key={i} style={{ flex:1, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:8, padding:"12px 14px" }}>
              <div style={{ fontSize:9.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.5, marginBottom:4, fontFamily:"Arial,sans-serif" }}>{t.label}</div>
              <div style={{ fontSize:22, fontWeight:800, color:t.color, fontFamily:"Arial,sans-serif" }}>{t.val}</div>
            </div>
          ))}
        </div>

        {/* Controls */}
        <div style={{ display:"flex", gap:10, alignItems:"center" }}>
          <input value={orderSearch} onChange={e=>setOrderSearch(e.target.value)} placeholder="Search orders or stores…" style={{ flex:1, padding:"8px 12px", borderRadius:7, border:`1px solid ${C.cardBord}`, background:C.cardBg, color:C.textPri, fontSize:12, fontFamily:"Arial,sans-serif", outline:"none" }}/>
          {["ALL",...ORDER_STATUSES].map(f=>(
            <button key={f} onClick={()=>setOrderFilter(f)}
              style={{ padding:"6px 12px", borderRadius:6, border:`1px solid ${orderFilter===f?C.gold:C.cardBord}`, background:orderFilter===f?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent", color:orderFilter===f?C.gold:C.textSec, fontSize:10.5, fontWeight:orderFilter===f?700:400, cursor:"pointer", fontFamily:"Arial,sans-serif", whiteSpace:"nowrap" }}>
              {f}
            </button>
          ))}
        </div>

        {/* Orders table */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden" }}>
          <table style={{ width:"100%", borderCollapse:"collapse" }}>
            <thead>
              <tr style={{ background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC" }}>
                {["Order ID","Store","State","Grade","Gallons","Terminal","Carrier","Status","Created","ETA","Cost/gal"].map(h=>(
                  <th key={h} style={{ fontSize:9.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.4, fontWeight:700, textAlign:["Gallons","Cost/gal"].includes(h)?"right":"left", padding:"9px 12px", borderBottom:`1px solid ${C.cardBord}`, fontFamily:"Arial,sans-serif" }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {filtered.map((o, oi)=>(
                <tr key={o.id} style={{ borderBottom:`1px solid ${C.cardBord}`, background:oi%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.015)") }}>
                  <td style={{ padding:"9px 12px", fontSize:10.5, fontWeight:700, color:C.gold, fontFamily:"Arial,sans-serif" }}>{o.id}</td>
                  <td style={{ padding:"9px 12px", fontSize:11, color:C.textPri, fontFamily:"Arial,sans-serif", maxWidth:160, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>{o.storeName}</td>
                  <td style={{ padding:"9px 12px", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif" }}>{o.state}</td>
                  <td style={{ padding:"9px 12px" }}><GradeTag grade={o.grade} darkMode={darkMode}/></td>
                  <td style={{ padding:"9px 12px", textAlign:"right", fontSize:11, fontFamily:"Arial,sans-serif", color:C.textPri }}>{o.gallons.toLocaleString()}</td>
                  <td style={{ padding:"9px 12px", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif" }}>{o.terminal}</td>
                  <td style={{ padding:"9px 12px", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif", maxWidth:130, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>{o.carrier}</td>
                  <td style={{ padding:"9px 12px" }}><StatusBadge status={o.status} darkMode={darkMode}/></td>
                  <td style={{ padding:"9px 12px", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif" }}>{o.created}</td>
                  <td style={{ padding:"9px 12px", fontSize:10.5, color:o.eta?C.green:C.textMut, fontFamily:"Arial,sans-serif" }}>{o.eta||"—"}</td>
                  <td style={{ padding:"9px 12px", textAlign:"right", fontSize:11, fontWeight:700, color:C.textPri, fontFamily:"Arial,sans-serif" }}>${o.contractCost.toFixed(4)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
    );
  };

  //  Tab: Inventory 
  const renderInventory = () => {
    const sortedStores = [...STORES].sort((a,b)=>{
      if(invSort==="daysSupply") {
        const minA = Math.min(...GRADES.map(g=>a.daysSupply[g]));
        const minB = Math.min(...GRADES.map(g=>b.daysSupply[g]));
        return minA - minB;
      }
      if(invSort==="state") return a.state.localeCompare(b.state);
      return a.name.localeCompare(b.name);
    }).filter(s => selectedState==="ALL" || s.state===selectedState);

    const reorderCount = STORES.filter(s=>GRADES.some(g=>s.daysSupply[g]<2)).length;
    const criticalCount = STORES.filter(s=>GRADES.some(g=>s.daysSupply[g]<1)).length;

    return (
      <div style={{ display:"flex", flexDirection:"column", gap:14 }}>
        {/* Summary */}
        <div style={{ display:"flex", gap:10 }}>
          {[
            { label:"Total Sites", val:STORES.length, color:C.textPri },
            { label:"Reorder Triggered", val:reorderCount, color:C.amber },
            { label:"Critical (< 1 day)", val:criticalCount, color:C.red },
            { label:"Total Tank Capacity", val:`${(STORES.reduce((a,s)=>a+Object.values(s.tanks).reduce((aa,b)=>aa+b,0),0)/1000).toFixed(0)}K gal`, color:C.blue },
          ].map((t,i)=>(
            <div key={i} style={{ flex:1, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:8, padding:"12px 14px" }}>
              <div style={{ fontSize:9.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.5, marginBottom:4, fontFamily:"Arial,sans-serif" }}>{t.label}</div>
              <div style={{ fontSize:22, fontWeight:800, color:t.color, fontFamily:"Arial,sans-serif" }}>{t.val}</div>
            </div>
          ))}
        </div>

        {/* Controls */}
        <div style={{ display:"flex", gap:10, alignItems:"center" }}>
          <span style={{ fontSize:11, color:C.textSec }}>Filter by State:</span>
          {["ALL","NC","SC","VA","GA","FL"].map(st=>(
            <button key={st} onClick={()=>setSelectedState(st)}
              style={{ padding:"5px 12px", borderRadius:6, border:`1px solid ${selectedState===st?C.blue:C.cardBord}`, background:selectedState===st?(darkMode?"rgba(59,130,246,.12)":"#EFF6FF"):"transparent", color:selectedState===st?C.blue:C.textSec, fontSize:11, fontWeight:selectedState===st?700:400, cursor:"pointer", fontFamily:"Arial,sans-serif" }}>
              {st}
            </button>
          ))}
          <div style={{ marginLeft:"auto", display:"flex", gap:8, alignItems:"center" }}>
            <span style={{ fontSize:11, color:C.textSec }}>Sort:</span>
            {[{id:"daysSupply",label:"Days Supply"},{id:"state",label:"State"},{id:"name",label:"Name"}].map(s=>(
              <button key={s.id} onClick={()=>setInvSort(s.id)}
                style={{ padding:"5px 10px", borderRadius:6, border:`1px solid ${invSort===s.id?C.gold:C.cardBord}`, background:invSort===s.id?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent", color:invSort===s.id?C.gold:C.textSec, fontSize:11, fontWeight:invSort===s.id?700:400, cursor:"pointer", fontFamily:"Arial,sans-serif" }}>
                {s.label}
              </button>
            ))}
          </div>
        </div>

        {/* Inventory table */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, overflow:"hidden" }}>
          <table style={{ width:"100%", borderCollapse:"collapse" }}>
            <thead>
              <tr style={{ background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC" }}>
                {["Site","State","Regular Inv","Days","Premium Inv","Days","Diesel Inv","Days","Min Days","Action"].map(h=>(
                  <th key={h} style={{ fontSize:9.5, color:C.textMut, textTransform:"uppercase", letterSpacing:.4, fontWeight:700, textAlign:"left", padding:"9px 12px", borderBottom:`1px solid ${C.cardBord}`, fontFamily:"Arial,sans-serif" }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {sortedStores.map((s, si)=>{
                const minDays = Math.min(...GRADES.map(g=>s.daysSupply[g]));
                const isCritical = minDays < 1;
                const isReorder = minDays < 2;
                return (
                  <tr key={s.id} style={{ borderBottom:`1px solid ${C.cardBord}`, background:isCritical?(darkMode?"rgba(248,113,113,.06)":"#FFF5F5"):isReorder?(darkMode?"rgba(251,191,36,.04)":"#FEFCE8"):(si%2===0?"transparent":(darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.015)")) }}>
                    <td style={{ padding:"8px 12px", fontSize:11, fontWeight:600, color:C.textPri, fontFamily:"Arial,sans-serif", maxWidth:160, overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>{s.name}</td>
                    <td style={{ padding:"8px 12px", fontSize:10.5, color:C.textSec }}>{s.state}</td>
                    {GRADES.map(g=>{
                      const pct = s.invLevel[g] / s.tanks[g];
                      const days = s.daysSupply[g];
                      const dc = days < 1 ? C.red : days < 2 ? C.amber : C.green;
                      return (<React.Fragment key={g}>
                        <td style={{ padding:"8px 12px", minWidth:110 }}>
                          <div style={{ fontSize:10.5, color:C.textPri, fontFamily:"Arial,sans-serif", marginBottom:3 }}>{s.invLevel[g].toLocaleString()} / {s.tanks[g].toLocaleString()} gal</div>
                          <InvBar pct={pct} color={C.green} C={C}/>
                        </td>
                        <td style={{ padding:"8px 12px", fontSize:11, fontWeight:700, color:dc, fontFamily:"Arial,sans-serif" }}>{days.toFixed(1)}d</td>
                      </React.Fragment>);
                    })}
                    <td style={{ padding:"8px 12px", fontSize:12, fontWeight:800, color:isCritical?C.red:isReorder?C.amber:C.green, fontFamily:"Arial,sans-serif" }}>{minDays.toFixed(1)}d</td>
                    <td style={{ padding:"8px 12px" }}>
                      {isReorder && (
                        <button style={{ fontSize:9.5, padding:"3px 10px", borderRadius:5, border:`1px solid ${isCritical?C.red:C.amber}`, background:isCritical?(darkMode?"rgba(248,113,113,.12)":"#FFF5F5"):(darkMode?"rgba(251,191,36,.12)":"#FEFCE8"), color:isCritical?C.red:C.amber, fontWeight:700, cursor:"pointer", fontFamily:"Arial,sans-serif" }}>
                          {isCritical?"URGENT ORDER":"Reorder"}
                        </button>
                      )}
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      </div>
    );
  };

  //  Tab: Pricing 
  const renderPricing = () => {
    const FONT = "Arial,sans-serif";
    const filteredStores = pricingState==="ALL" ? STORES : STORES.filter(s=>s.state===pricingState);

    return (
      <div style={{ display:"flex", flexDirection:"column", gap:14 }}>

        {/* State filter — controls which stores feed the table */}
        <div style={{ display:"flex", gap:10, alignItems:"center" }}>
          <span style={{ fontSize:11, color:C.textSec, fontFamily:"Arial,sans-serif", fontWeight:600 }}>State:</span>
          {["ALL","NC","SC","VA","GA","FL"].map(st=>(
            <button key={st} onClick={()=>setPricingState(st)}
              style={{ padding:"5px 12px", borderRadius:6, border:`1px solid ${pricingState===st?C.gold:C.cardBord}`, background:pricingState===st?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent", color:pricingState===st?C.gold:C.textSec, fontSize:11, fontWeight:pricingState===st?700:400, cursor:"pointer", fontFamily:"Arial,sans-serif" }}>
              {st}
            </button>
          ))}
        </div>

        {/* Unified competitor + financial table */}
        <PricingLiveCompetitors
          stores={filteredStores}
          darkMode={darkMode} C={C} FONT={FONT}
        />
      </div>
    );
  };

  //  Tab: Analytics 
  const renderAnalytics = () => {
    const byState = ["NC","SC","VA","GA","FL"].map(st=>{
      const ss = STORES.filter(s=>s.state===st);
      const vol = ss.reduce((a,s)=>a+s.totalDailyVol,0);
      const margin = ss.length ? ss.reduce((a,s)=>a+s.blendedMargin,0)/ss.length : 0;
      const gross = ss.reduce((a,s)=>a+s.blendedMargin*s.totalDailyVol*30,0);
      return { state:st, count:ss.length, vol, margin, gross };
    });

    const byGrade = GRADES.map(g=>{
      const vol = STORES.reduce((a,s)=>a+s.dailyVol[g],0);
      const margin = STORES.reduce((a,s)=>a+s.marginPerGrade[g],0)/STORES.length;
      return { grade:g, vol, margin };
    });

    const byTerminal = TERMINALS.map(t=>{
      const ss = STORES.filter(s=>s.terminal===t.id);
      const vol = ss.reduce((a,s)=>a+s.totalDailyVol,0);
      const margin = ss.length ? ss.reduce((a,s)=>a+s.blendedMargin,0)/ss.length : 0;
      return { term:t, count:ss.length, vol, margin };
    });

    const GRADE_COL = { Regular:"#3B82F6", Premium:"#8B5CF6", Diesel:"#F59E0B" };
    const STATE_COL = { NC:"#3B82F6", SC:"#10B981", VA:"#8B5CF6", GA:"#F59E0B", FL:"#EF4444" };

    return (
      <div style={{ display:"flex", flexDirection:"column", gap:14 }}>
        {/* Top row: State volume + margin */}
        <div style={{ display:"flex", gap:14 }}>
          <div style={{ flex:1, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
            <SectionHeader title="Monthly Gross Margin by State" sub="30-day projected · $/month" C={C}/>
            {byState.map((s,i)=>(
              <div key={s.state} style={{ marginBottom:10 }}>
                <div style={{ display:"flex", justifyContent:"space-between", marginBottom:3 }}>
                  <span style={{ fontSize:11, color:C.textPri, fontWeight:600, fontFamily:"Arial,sans-serif" }}>{s.state} · {s.count} sites</span>
                  <span style={{ fontSize:11, fontWeight:700, color:STATE_COL[s.state], fontFamily:"Arial,sans-serif" }}>${(s.gross/1000).toFixed(0)}K</span>
                </div>
                <div style={{ height:8, background:C.cardBord, borderRadius:4, overflow:"hidden" }}>
                  <div style={{ height:"100%", width:`${(s.gross/Math.max(...byState.map(x=>x.gross)))*100}%`, background:STATE_COL[s.state], borderRadius:4 }}/>
                </div>
                <div style={{ fontSize:10, color:C.textSec, marginTop:2 }}>{(s.vol/1000).toFixed(0)}K gal/day · avg ${s.margin.toFixed(4)}/gal</div>
              </div>
            ))}
          </div>

          <div style={{ flex:1, background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
            <SectionHeader title="Volume & Margin by Grade" sub="All 60 stores · Daily" C={C}/>
            <div style={{ display:"flex", gap:10, marginBottom:16 }}>
              {byGrade.map(g=>(
                <div key={g.grade} style={{ flex:1, background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC", borderRadius:8, padding:"10px 12px", border:`1px solid ${C.cardBord}`, textAlign:"center" }}>
                  <GradeTag grade={g.grade} darkMode={darkMode}/>
                  <div style={{ fontSize:17, fontWeight:800, color:GRADE_COL[g.grade], fontFamily:"Arial,sans-serif", marginTop:8 }}>{(g.vol/1000).toFixed(0)}K</div>
                  <div style={{ fontSize:10, color:C.textSec, marginTop:2 }}>gal/day</div>
                  <div style={{ fontSize:12, fontWeight:700, color:C.green, fontFamily:"Arial,sans-serif", marginTop:4 }}>${g.margin.toFixed(4)}/gal</div>
                </div>
              ))}
            </div>
            <SectionHeader title="By Terminal Coverage" C={C}/>
            {byTerminal.map(bt=>(
              <div key={bt.term.id} style={{ display:"flex", alignItems:"center", gap:10, marginBottom:8 }}>
                <div style={{ width:32, textAlign:"center", fontSize:10, fontWeight:700, color:C.textSec, fontFamily:"Arial,sans-serif" }}>{bt.term.short}</div>
                <div style={{ flex:1 }}>
                  <div style={{ display:"flex", justifyContent:"space-between", marginBottom:2 }}>
                    <span style={{ fontSize:10, color:C.textSec }}>{bt.count} stores · {(bt.vol/1000).toFixed(0)}K gal/day</span>
                    <span style={{ fontSize:10.5, fontWeight:700, color:C.gold, fontFamily:"Arial,sans-serif" }}>${bt.margin.toFixed(4)}/gal</span>
                  </div>
                  <InvBar pct={bt.count/STORES.length} color={C.gold} C={C}/>
                </div>
              </div>
            ))}
          </div>
        </div>

        {/* NYMEX 30-day full chart */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
          <SectionHeader title="30-Day NYMEX Futures" sub="ULSD · RBOB · WTI Crude (÷10) · $/gal" C={C}
            action={
              <div style={{ display:"flex", gap:14, fontSize:10.5, fontFamily:"Arial,sans-serif" }}>
                {[{l:"ULSD",c:"#3B82F6"},{l:"RBOB",c:"#10B981"},{l:"Crude/10",c:"#F4D398"}].map(s=>(
                  <div key={s.l} style={{ display:"flex", alignItems:"center", gap:4 }}>
                    <div style={{ width:16, height:2, background:s.c, borderRadius:1 }}/>
                    <span style={{ color:C.textSec }}>{s.l}</span>
                  </div>
                ))}
              </div>
            }
          />
          <div style={{ height:120 }}>
            <MultiLine series={[
              { data:NYMEX.ulsd, color:"#3B82F6" },
              { data:NYMEX.rbob, color:"#10B981" },
              { data:NYMEX.crude.map(v=>v/10), color:"#F4D398", dash:"4,3" },
            ]} h={120} C={C} darkMode={darkMode}/>
          </div>
        </div>

        {/* Top 10 sites by gross margin */}
        <div style={{ background:C.cardBg, border:`1px solid ${C.cardBord}`, borderRadius:10, padding:16 }}>
          <SectionHeader title="Top 10 Sites by Monthly Gross Margin" sub="Blended margin × daily volume × 30 days" C={C}/>
          <div style={{ display:"flex", flexDirection:"column", gap:6 }}>
            {[...STORES].sort((a,b)=>(b.blendedMargin*b.totalDailyVol)-(a.blendedMargin*a.totalDailyVol)).slice(0,10).map((s,i)=>{
              const monthly = s.blendedMargin * s.totalDailyVol * 30;
              const maxMonthly = STORES[0] ? STORES.reduce((a,x)=>Math.max(a,x.blendedMargin*x.totalDailyVol*30),0) : 1;
              return (
                <div key={s.id} style={{ display:"flex", alignItems:"center", gap:10 }}>
                  <div style={{ width:20, textAlign:"right", fontSize:10.5, fontWeight:700, color:i<3?C.gold:C.textMut, fontFamily:"Arial,sans-serif" }}>{i+1}</div>
                  <div style={{ width:180, fontSize:11, color:C.textPri, fontFamily:"Arial,sans-serif", overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>{s.name}</div>
                  <div style={{ width:30, fontSize:10, color:C.textSec }}>{s.state}</div>
                  <div style={{ flex:1 }}>
                    <div style={{ height:6, background:C.cardBord, borderRadius:3, overflow:"hidden" }}>
                      <div style={{ height:"100%", width:`${(monthly/maxMonthly)*100}%`, background:i<3?C.gold:C.green, borderRadius:3 }}/>
                    </div>
                  </div>
                  <div style={{ width:70, textAlign:"right", fontSize:11, fontWeight:700, color:i<3?C.gold:C.green, fontFamily:"Arial,sans-serif" }}>${(monthly/1000).toFixed(1)}K</div>
                  <div style={{ width:80, textAlign:"right", fontSize:10.5, color:C.textSec, fontFamily:"Arial,sans-serif" }}>${s.blendedMargin.toFixed(4)}/gal</div>
                </div>
              );
            })}
          </div>
        </div>
      </div>
    );
  };

  //  Render tab content 
  const renderTab = () => {
    switch(activeTab) {
      case "command":   return renderDashboard();
      case "plan":      return renderPlan();
      case "rack":      return renderRackPrices();
      case "bestbuy":   return renderBestBuy();
      case "contracts": return renderContracts();
      case "forecast":  return renderForecast();
      case "inventory": return renderInventory();
      case "dispatch":  return renderDispatch();
      case "strategy":  return renderStrategy();
      case "pricing":   return renderPricing();
      case "procurement": return renderProcurement();
      case "replenmap":   return renderReplenMap();
      default:          return renderDashboard();
    }
  };

  //  Tab: Procurement 
  // ── Tab: Daily Plan Optimizer ──────────────────────────────────────────────
  const renderPlan = () => {
    const FONT = "Arial,sans-serif";
    return (
      <DailyPlanOptimizer
        liveLoads={liveLoads}
        planFilter={planFilter}
        onClearPlanFilter={() => setPlanFilter(null)}
        onOpenDispatch={(row)=>{
          // Use the user's CURRENTLY CHOSEN terminal — which may be the
          // algorithm's pick or their manual override.
          setDispatchTarget({
            storeId:   row.store.id,
            grade:     row.grade,
            vol:       row.vol,
            storeName: row.store.name,
            terminal:  row.chosen.terminal.id,
            // Supplier context for the dispatch modal and the resulting BOL
            supplierId:     row.chosen.supplier.id,
            supplierShort:  row.chosen.supplier.short,
            supplierName:   row.chosen.supplier.name,
            isSpot:         row.chosen.isSpot,
            contractStatus: row.chosen.contractStatus,
          });
          setDispatchCarrierId(row.carrier?.id || null);
          setDispatchTruckId(null);
          // Crumb tells the dispatcher where this load came from and why
          const savingsNote = row.savingsTotal > 0
            ? `$${Math.round(row.savingsTotal).toLocaleString()} saved`
            : row.savingsTotal < 0
              ? `$${Math.round(Math.abs(row.savingsTotal)).toLocaleString()} over baseline`
              : "baseline pick";
          const overrideNote = row.isOverridden ? " · manual override" : "";
          setDispatchCrumb(`Plan Optimizer · ${row.store.name} · ${row.chosen.terminal.short}/${row.chosen.supplier.short}${overrideNote} · ${savingsNote}`);
          setShowDispatchModal(true);
        }}
        onPublishDay={(trips, assignments) => {
          // Turn each trip's stops into SCHEDULED loads in the live feed.
          // Each stop = one delivery row. Multi-stop trips share trip ID,
          // truck, driver, and depart time, but get sequential ETAs.
          const newLoads = [];
          let nextLoadNum = 4500 + liveLoads.length;
          // Day-publish anchors trips to start at 6 AM, staggered every 90 min
          // per driver so multiple trips for one driver don't collide visually.
          const driverNextStartMin = {}; // truck unit → minutes-since-midnight
          trips.forEach((trip, ti) => {
            const assigned = assignments[trip.id];
            if (!assigned) return; // unassignable — skip
            const carrier = assigned.carrier;
            const tractor = assigned.tractor;
            const driverKey = `${carrier.short}|${tractor.unit}`;
            const startMin = driverNextStartMin[driverKey] ?? (6*60 + ti*5);
            // 25 min loading + ~30 min terminal-to-first-stop + 25 min per drop
            let curMin = startMin + 25; // depart after loading
            const departTime = `${String(Math.floor(curMin/60)).padStart(2,"0")}:${String(curMin%60).padStart(2,"0")}`;
            trip.stops.forEach((stop, si) => {
              // Each stop: ~45 min from prior point + 25 min unload
              const driveMin = si === 0 ? 45 : 35;
              curMin += driveMin;
              const etaMin = curMin;
              curMin += 25; // unload time before next leg
              const eta = `${String(Math.floor(etaMin/60)).padStart(2,"0")}:${String(etaMin%60).padStart(2,"0")}`;
              newLoads.push({
                id: `LD-${nextLoadNum++}`,
                tripId: trip.id,
                stopNum: si + 1,
                stopCount: trip.stops.length,
                carrier: carrier.short,
                truck: tractor.unit,
                driver: tractor.driver,
                origin: `${trip.terminal.name.split(",")[0]}, ${trip.terminal.short}`,
                dest: stop.store.name,
                grade: stop.grade,
                gals: stop.vol,
                status: "SCHEDULED",
                pct: 0,
                bol: null,
                tempF: null,
                apiGravity: null,
                bsmtTicket: null,
                eta,
                departed: si === 0 ? departTime : null,
                detained: 0,
                publishedFromPlan: true, // marker so UI can highlight
              });
            });
            // Driver's next available slot: end of this trip + 30 min buffer
            driverNextStartMin[driverKey] = curMin + 30;
          });
          setLiveLoads(prev => [...prev, ...newLoads]);
          // Push the user to Day Schedule so they see the result instantly
          setActiveTab("dispatch");
          setDispatchTab("day");
        }}
        darkMode={darkMode} C={C} FONT={FONT}
      />
    );
  };

  // ── Tab: Replenishment Map ──────────────────────────────────────────────────
  const renderReplenMap = () => {
    const FONT = "Arial,sans-serif";
    return (
      <ReplenMapPage
        darkMode={darkMode} C={C} FONT={FONT}
        mapFilter={mapFilter} setMapFilter={setMapFilter}
        mapGrade={mapGrade}   setMapGrade={setMapGrade}
        hoveredStore={hoveredStore}   setHoveredStore={setHoveredStore}
        selectedStore={selectedStore} setSelectedStore={setSelectedStore}
        liveLoads={liveLoads}
        onDispatch={(payload)=>{
          setDispatchTarget({storeId:payload.storeId,grade:payload.grade,vol:payload.vol,storeName:payload.storeName,terminal:payload.terminal});
          setDispatchCarrierId(payload.carrierId||null);
          setDispatchTruckId(null);
          setShowDispatchModal(true);
        }}
      />
    );
  };

  const renderProcurement = () => {
    const FONT = "Arial,sans-serif";

    //  AI Sourcing 
    const runAISourcing = async (grade, vol, terminal) => {
      setAiSourcingLoading(true);
      setAiSourcingResult(null);
      try {
        const supplierContext = SUPPLIERS.filter(s=>s.terminals.includes(terminal)&&s.grades.includes(grade)).map(s=>({
          name:s.name, tier:s.tier, pricingBasis:s.pricingBasis, creditTerms:s.creditTerms,
          performanceScore:s.performanceScore, incidents:s.incidents, contractType:s.contractType,
          ytdVolume:s.ytdVolume, contractExpiry:s.contractExpiry,
          currentRack: RACK_PRICES[terminal]?.[grade], diff: CONTRACT_DIFF[terminal]?.[grade],
        }));
        const termSig = SIGNALS[terminal]?.[grade];
        const altOptions = ALT_SUPPLY_POINTS.filter(sp=>sp.availableGrades.includes(grade)).map(sp=>({
          name:sp.name, type:sp.type, leadDays:sp.leadDays,
          spotLanded: altLandedCost(sp,grade,STATE_TAX.NC)?.spot,
        })).slice(0,4);
        const prompt = `You are a senior fuel procurement advisor. Give a specific buy recommendation.

REQUEST: ${vol.toLocaleString()} gal ${grade} at ${TERMINALS.find(t=>t.id===terminal)?.name}
MARKET SIGNAL: ${termSig?.signal} — ${termSig?.reason}
RACK TODAY: $${RACK_PRICES[terminal]?.[grade]?.toFixed(4)}/gal
3-DAY TREND: ${termSig?.trend3d>0?" +":" "}$${Math.abs(termSig?.trend3d||0).toFixed(4)}/gal
14-DAY FORECAST: $${FORWARD[terminal]?.[grade]?.[6]?.val?.toFixed(4)}/gal at day 7

SUPPLIERS AT THIS TERMINAL:
${JSON.stringify(supplierContext,null,1)}

ALTERNATIVE SUPPLY OPTIONS:
${JSON.stringify(altOptions,null,1)}

UNHEDGED EXPOSURE: ${(UNHEDGED/1000).toFixed(0)}K gal/month

Respond ONLY with JSON (no markdown):
{"recommendedSupplier":"supplier name","recommendedSource":"contract|spot|alt_supply","recommendedTiming":"buy now|wait 3 days|wait 7 days","landedCost":3.4523,"reasoning":"2-3 sentences with specific data","riskNote":"one risk","hedgeSuggestion":"one sentence on hedge posture","potentialSavings":4200}`;

        const res = await fetch("https://api.anthropic.com/v1/messages",{
          method:"POST",
          headers:{"Content-Type":"application/json","anthropic-dangerous-direct-browser-access":"true","anthropic-version":"2023-06-01"},
          body:JSON.stringify({model:"claude-sonnet-4-6",max_tokens:500,messages:[{role:"user",content:prompt}]}),
        });
        const data = await res.json();
        const raw = data.content?.[0]?.text||"{}";
        const parsed = JSON.parse(raw.replace(/```json|```/g,"").trim());
        setAiSourcingResult({...parsed, grade, vol, terminal});
        addToast(" AI sourcing recommendation ready");
      } catch(e) {
        setAiSourcingResult({error:"Add your Anthropic API key to enable AI sourcing."});
      }
      setAiSourcingLoading(false);
    };

    //  Landed cost calculator 
    const calcLanded = (supplierId, terminal, grade, gals) => {
      const supplier = SUPPLIERS.find(s=>s.id===supplierId);
      if(!supplier) return null;
      const rack    = RACK_PRICES[terminal]?.[grade]||0;
      const diff    = CONTRACT_DIFF[terminal]?.[grade]||0;
      const freight = FREIGHT[terminal]||0;
      const tariff  = COLONIAL.tariffs[terminal]?.[grade==="Diesel"?"distillate":"gasoline"]||0;
      const stTax   = STATE_TAX.NC; // default NC — real impl would vary by delivery state
      const contract= rack + diff;
      const landed  = contract + tariff + freight + stTax + FED_TAX;
      const spotL   = rack + 0.0285 + tariff + freight + stTax + FED_TAX;
      const freight$ = gals * freight;
      const tariff$  = gals * tariff;
      const total    = gals * landed;
      return { rack, diff, contract, tariff, freight, stTax, fedTax:FED_TAX, landed, spotLanded:spotL, freight$, tariff$, total, gals };
    };

    //  PO helpers 
    const createPO = () => {
      const lc = calcLanded(newPO.supplierId, newPO.terminal, newPO.grade, newPO.gals);
      const supplier = SUPPLIERS.find(s=>s.id===newPO.supplierId);
      const id = "PO-2504-" + String(pos.length+1).padStart(3,"0");
      setPos(prev=>[{
        id, supplierId:newPO.supplierId, terminal:newPO.terminal,
        grade:newPO.grade, gals:newPO.gals,
        pricePerGal:lc?.contract||0, totalCost:lc?.total||0,
        status:"DRAFT", created:"Apr 16", delivery:newPO.deliveryDate,
        invoiced:false, notes:newPO.notes, isNew:true,
      },...prev]);
      setShowPOModal(false);
      addToast(` ${id} created — ${supplier?.short} · ${newPO.grade} · ${newPO.gals.toLocaleString()} gal`);
    };

    const poStatusColor = s => s==="DELIVERED"?"#059669":s==="LOADING"?"#4F46E5":s==="CONFIRMED"?"#0891B2":s==="DRAFT"?"#64748B":s==="PENDING"?"#F59E0B":"#EF4444";
    const poStatusBg    = s => ({
      DELIVERED:darkMode?"rgba(5,150,105,.14)":"#ECFDF5",
      LOADING:  darkMode?"rgba(79,70,229,.14)":"#F0FDFA",
      CONFIRMED:darkMode?"rgba(8,145,178,.14)":"#ECFEFF",
      DRAFT:    darkMode?"rgba(100,116,139,.10)":"#F8FAFC",
      PENDING:  darkMode?"rgba(245,158,11,.14)":"#F8FAFB",
    }[s]||"transparent");

    const totalCommitted = pos.filter(p=>!["DELIVERED"].includes(p.status)).reduce((a,p)=>a+p.totalCost,0);
    const totalDelivered = pos.filter(p=>p.status==="DELIVERED").reduce((a,p)=>a+p.totalCost,0);
    const openPOs        = pos.filter(p=>!["DELIVERED"].includes(p.status)).length;
    const draftPOs       = pos.filter(p=>p.status==="DRAFT").length;
    const triggeredAlerts= alerts.filter(a=>a.triggered&&a.active).length;

    const subTabs = [
      {id:"suppliers",  label:"Suppliers",        icon:""},
      {id:"rack",       label:"Rack Monitor",      icon:""},
      {id:"po",         label:"Purchase Orders",   icon:""},
      {id:"landed",     label:"Landed Cost Calc",  icon:""},
      {id:"ai",         label:"AI Sourcing",       icon:"", badge:"Phase 2"},
      {id:"hedging",    label:"Hedging",           icon:"", badge:"Phase 2"},
    ];

    return (
      <div style={{display:"flex",flexDirection:"column",gap:12}}>

        {/* KPI strip */}
        <div style={{display:"flex",gap:8}}>
          {[
            {label:"Open POs",           val:openPOs,                                                color:C.blue,    sub:`${draftPOs} awaiting approval`},
            {label:"Committed Spend",    val:`$${(totalCommitted/1000).toFixed(0)}K`,               color:C.gold,    sub:"this cycle"},
            {label:"YTD Supplier Spend", val:`$${(SUPPLIERS.reduce((a,s)=>a+s.ytdSpend,0)/1000000).toFixed(1)}M`, color:C.textPri, sub:"all suppliers"},
            {label:"Price Alerts",       val:triggeredAlerts,                                        color:triggeredAlerts>0?C.red:C.green, sub:`${alerts.filter(a=>a.active).length} active`},
            {label:"Active Contracts",   val:SUPPLIERS.filter(s=>s.contractType.includes("Annual")).length, color:C.green, sub:"annual volume deals"},
          ].map((k,i)=><KpiCard key={i} {...k} C={C} darkMode={darkMode} glass={true}/>)}
        </div>

        {/* Sub-nav */}
        <div style={{display:"flex",gap:4,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:8,padding:4}}>
          {subTabs.map(t=>(
            <button key={t.id} onClick={()=>setProcTab(t.id)}
              style={{flex:1,padding:"7px 6px",borderRadius:6,border:"none",cursor:"pointer",fontFamily:FONT,fontSize:11,fontWeight:procTab===t.id?700:500,
                background:procTab===t.id?"#0D1B2A":"transparent",
                color:procTab===t.id?"#F4D398":C.textMut,
                transition:"all .15s",position:"relative",
                }}>
              {t.icon} {t.label}
              {t.badge&&<span style={{marginLeft:4,fontSize:7.5,fontWeight:700,padding:"1px 4px",borderRadius:4,background:"#0D9488",color:"#fff",verticalAlign:"middle"}}>{t.badge}</span>}
            </button>
          ))}
        </div>

        {/*  SUPPLIERS  */}
        {procTab==="suppliers"&&(
          <div style={{display:"flex",flexDirection:"column",gap:12}}>

            {/* Supplier cards */}
            <div style={{display:"grid",gridTemplateColumns:"repeat(3,1fr)",gap:12}}>
              {SUPPLIERS.map(s=>{
                const perf = computeSupplierScore(s);
                const score = perf.total;
                const perfColor = score>=90?C.green:score>=80?C.amber:"#DC2626";
                const tierLabel = s.tier===1?"Direct Refiner":s.tier===2?"Jobber":"Spot Only";
                const tierBg = s.tier===1?"#E0E1DD":s.tier===2?"#E0E1DD":"transparent";
                const termBadges = s.terminals.map(tid=>{
                  const t = TERMINALS.find(t=>t.id===tid);
                  return t ? { id:tid, short:t.short } : { id:tid, short:tid };
                });
                const showScoreTooltip = hoveredScoreId === s.id;
                return (
                  <div key={s.id} style={{
                    background:C.cardBg,
                    border:`1px solid ${s.incidents>0?C.amber+"50":C.cardBord}`,
                    borderRadius:12, overflow:"hidden",
                    display:"flex", flexDirection:"column",
                  }}>
                    {/* Card header — logo + name + score */}
                    <div style={{
                      padding:"14px 16px 12px",
                      borderBottom:`1px solid ${C.cardBord}`,
                      display:"flex", alignItems:"center", justifyContent:"space-between", gap:12,
                    }}>
                      <div style={{display:"flex",alignItems:"center",gap:10,minWidth:0}}>
                        <SupplierLogo supplierName={s.name} supplierShort={s.short} size={36}/>
                        <div style={{minWidth:0}}>
                          <div style={{fontSize:12,fontWeight:800,color:C.textPri,fontFamily:FONT,whiteSpace:"nowrap",overflow:"hidden",textOverflow:"ellipsis"}}>{s.name}</div>
                          <div style={{display:"flex",gap:5,marginTop:4,flexWrap:"wrap"}}>
                            <span style={{fontSize:8.5,fontWeight:700,padding:"2px 7px",borderRadius:4,background:tierBg,color:"#0D1B2A"}}>{tierLabel}</span>
                            <span style={{display:"inline-flex",alignItems:"center",gap:4,flexWrap:"wrap"}}>
                              {termBadges.map(tb=>(
                                <span key={tb.id} style={{display:"inline-flex",alignItems:"center",gap:3,fontSize:8.5,fontWeight:600,padding:"2px 6px",borderRadius:4,background:darkMode?"rgba(255,255,255,.05)":"#F1F5F9",color:C.textSec}}>
                                  <ZoneBadge terminalId={tb.id}/>{tb.short}
                                </span>
                              ))}
                            </span>
                            {s.incidents>0&&<span style={{fontSize:8.5,fontWeight:700,padding:"2px 7px",borderRadius:4,background:"rgba(251,191,36,.1)",color:C.amber}}>{s.incidents} incident{s.incidents>1?"s":""}</span>}
                          </div>
                        </div>
                      </div>
                      {/* Score with hover tooltip */}
                      <div style={{textAlign:"center",flexShrink:0,position:"relative"}}
                        onMouseEnter={()=>setHoveredScoreId(s.id)}
                        onMouseLeave={()=>setHoveredScoreId(null)}>
                        {/* Score ring */}
                        <svg width={52} height={52} viewBox="0 0 52 52">
                          <circle cx={26} cy={26} r={21} fill="none" stroke={darkMode?"rgba(255,255,255,.06)":"#E8ECF0"} strokeWidth={5}/>
                          <circle cx={26} cy={26} r={21} fill="none" stroke={perfColor} strokeWidth={5}
                            strokeDasharray={`${2*Math.PI*21*score/100} ${2*Math.PI*21}`}
                            strokeLinecap="round"
                            transform="rotate(-90 26 26)" opacity={.9}/>
                          <text x={26} y={30} textAnchor="middle" fontSize={13} fontWeight={900}
                            fill={perfColor} fontFamily="Arial,sans-serif">{score}</text>
                        </svg>
                        <div style={{fontSize:7.5,color:C.textMut,textTransform:"uppercase",letterSpacing:.6,marginTop:1}}>score</div>
                        {/* Breakdown tooltip */}
                        {showScoreTooltip && (
                          <div style={{
                            position:"fixed", zIndex:9999,
                            width:240, right:"auto", top:"auto",
                            background:darkMode?"#0D1421":"#fff",
                            border:`1px solid ${C.cardBord}`,
                            borderRadius:10, padding:"12px 14px",
                            boxShadow:"0 8px 32px rgba(0,0,0,.25)",
                            fontFamily:FONT, textAlign:"left",
                            transform:"translate(-220px, -200px)",
                            pointerEvents:"none",
                          }}>
                            <div style={{fontSize:10.5,fontWeight:800,color:C.textPri,marginBottom:10}}>
                              Performance Score Breakdown
                            </div>
                            {perf.breakdown.map((b,bi)=>(
                              <div key={bi} style={{marginBottom:8}}>
                                <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:3}}>
                                  <span style={{fontSize:9.5,color:C.textSec,fontWeight:600}}>{b.label}</span>
                                  <span style={{fontSize:9.5,fontWeight:800,color:b.score/b.max>=0.85?"#16A34A":b.score/b.max>=0.6?"#F59E0B":"#DC2626"}}>
                                    {b.score}/{b.max}
                                  </span>
                                </div>
                                <div style={{height:4,borderRadius:2,background:darkMode?"rgba(255,255,255,.06)":"#E8ECF0",overflow:"hidden"}}>
                                  <div style={{height:"100%",width:`${b.score/b.max*100}%`,borderRadius:2,
                                    background:b.score/b.max>=0.85?"#16A34A":b.score/b.max>=0.6?"#F59E0B":"#DC2626"}}/>
                                </div>
                                <div style={{fontSize:8.5,color:C.textMut,marginTop:2,lineHeight:1.4}}>{b.note}</div>
                              </div>
                            ))}
                            <div style={{borderTop:`1px solid ${C.cardBord}`,paddingTop:8,marginTop:4,display:"flex",justifyContent:"space-between"}}>
                              <span style={{fontSize:9,color:C.textMut}}>Computed from live data</span>
                              <span style={{fontSize:10,fontWeight:800,color:perfColor}}>{score}/100</span>
                            </div>
                          </div>
                        )}
                      </div>
                    </div>

                    {/* Stats grid */}
                    <div style={{padding:"10px 16px",display:"grid",gridTemplateColumns:"1fr 1fr",gap:"8px 16px",borderBottom:`1px solid ${C.cardBord}`}}>
                      {[
                        {l:"Grades",       v:s.grades.join(", ")},
                        {l:"Credit Terms", v:s.creditTerms},
                        {l:"Credit Limit", v:`$${(s.creditLimit/1000000).toFixed(1)}M`},
                        {l:"YTD Volume",   v:`${(s.ytdVolume/1000000).toFixed(2)}M gal`},
                        {l:"YTD Spend",    v:`$${(s.ytdSpend/1000000).toFixed(2)}M`},
                        {l:"Contract",     v:s.contractType},
                        {l:"Expiry",       v:s.contractExpiry},
                        {l:"Min Vol/Mo",   v:s.minMonthlyVol>0?`${(s.minMonthlyVol/1000).toFixed(0)}K gal`:"None"},
                      ].map((row,ri)=>(
                        <div key={ri}>
                          <div style={{fontSize:8,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,marginBottom:1}}>{row.l}</div>
                          <div style={{fontSize:10.5,fontWeight:600,color:C.textPri,fontFamily:FONT,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{row.v}</div>
                        </div>
                      ))}
                    </div>

                    {/* Contacts */}
                    <div style={{padding:"8px 16px",borderBottom:`1px solid ${C.cardBord}`}}>
                      {s.contacts.map((c,ci)=>(
                        <div key={ci} style={{display:"flex",justifyContent:"space-between",alignItems:"center",padding:"3px 0"}}>
                          <div>
                            <span style={{fontSize:10.5,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{c.name}</span>
                            <span style={{fontSize:9,color:C.textMut,marginLeft:6}}>{c.role}</span>
                          </div>
                          <span style={{fontSize:9.5,color:"#3E6387",fontWeight:600}}>{c.phone}</span>
                        </div>
                      ))}
                    </div>

                    {/* Notes */}
                    <div style={{padding:"8px 16px",fontSize:9.5,color:C.textSec,lineHeight:1.5,flex:1}}>{s.notes}</div>

                    {/* Actions */}
                    <div style={{padding:"10px 16px 12px",display:"flex",gap:8,borderTop:`1px solid ${C.cardBord}`}}>
                      <button onClick={()=>{setNewPO(p=>({...p,supplierId:s.id,terminal:s.terminals[0]}));setShowPOModal(true);}}
                        style={{flex:1,padding:"8px 0",borderRadius:7,border:"none",
                          background:"#E0E1DD",color:"#386387",
                          fontSize:10.5,fontWeight:700,cursor:"pointer",fontFamily:FONT,
                          letterSpacing:.2}}>
                        + Create PO
                      </button>
                      <button onClick={()=>{setProcTab("ai");runAISourcing(s.grades[0],100000,s.terminals[0]);}}
                        style={{padding:"8px 14px",borderRadius:7,
                          border:`1px solid ${C.cardBord}`,
                          background:"transparent",color:C.textSec,
                          fontSize:10.5,cursor:"pointer",fontFamily:FONT}}>
                        Source
                      </button>
                    </div>
                  </div>
                );
              })}
            </div>
          </div>
        )}

        {/*  RACK MONITOR  */}
        {procTab==="rack"&&(
          <div style={{display:"flex",flexDirection:"column",gap:12}}>

            {/* Price alert strip */}
            {alerts.filter(a=>a.active&&a.triggered).length>0&&(
              <div style={{background:darkMode?"rgba(239,68,68,.1)":"#FFF5F5",border:`1px solid ${C.red}40`,borderRadius:10,padding:"12px 16px",display:"flex",alignItems:"center",gap:12}}>
                <span style={{fontSize:18}}></span>
                <div>
                  <div style={{fontSize:12,fontWeight:700,color:C.red,fontFamily:FONT}}>Price Alerts Triggered</div>
                  <div style={{fontSize:10.5,color:C.textSec,marginTop:2}}>{alerts.filter(a=>a.active&&a.triggered).map(a=>`${TERMINALS.find(t=>t.id===a.terminal)?.short} ${a.grade} (${a.type} $${a.threshold})`).join(" · ")}</div>
                </div>
                <button onClick={()=>setProcTab("ai")} style={{marginLeft:"auto",padding:"6px 14px",borderRadius:6,border:`1px solid ${C.red}`,background:darkMode?"rgba(239,68,68,.12)":"#FFF5F5",color:C.red,fontSize:10.5,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                  Run AI Sourcing →
                </button>
              </div>
            )}

            {/* Full price matrix */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:14}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT}}>Live Rack Price Matrix — All Terminals × Grades</div>
                <div style={{fontSize:10,color:C.textSec}}>OPIS · Updated 09:22 CT · Prices in $/gal</div>
              </div>
              <table style={{width:"100%",borderCollapse:"collapse"}}>
                <thead>
                  <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                    {["Terminal","Pipeline","Supplier","Regular","Premium","Diesel","Signal","30d Trend","Actions"].map(h=>(
                      <th key={h} style={{padding:"8px 12px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                    ))}
                  </tr>
                </thead>
                <tbody>
                  {TERMINALS.map((t,ti)=>{
                    const sig = SIGNALS[t.id]?.Regular;
                    const hist = RACK_HISTORY[t.id]?.Regular||[];
                    const trend30 = hist.length>1 ? hist[hist.length-1]-hist[0] : 0;
                    const supplier = SUPPLIERS.find(s=>s.terminals.includes(t.id)&&s.tier===1);
                    return (
                      <tr key={t.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:ti%2===0?"transparent":darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)"}}>
                        <td style={{padding:"10px 12px"}}>
                          <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,display:"flex",alignItems:"center",gap:5}}><ZoneBadge terminalId={t.id}/>{t.short}</div>
                          <div style={{fontSize:9.5,color:C.textMut}}>{t.name}</div>
                        </td>
                        <td style={{padding:"10px 12px",fontSize:10.5,color:C.textSec}}>{t.pipeline}</td>
                        <td style={{padding:"10px 12px"}}>
                          {supplier
                            ? <SupplierLogo supplierName={supplier.name} supplierShort={supplier.short} size={supplier.name==="ExxonMobil"?35:28}/>
                            : <span style={{fontSize:10.5,color:C.textMut}}>—</span>}
                        </td>
                        {GRADES.map(g=>{
                          const rack = RACK_PRICES[t.id]?.[g];
                          const diff = CONTRACT_DIFF[t.id]?.[g];
                          const gsig = SIGNALS[t.id]?.[g];
                          const alert = alerts.find(a=>a.terminal===t.id&&a.grade===g&&a.active);
                          return (
                            <td key={g} style={{padding:"10px 12px"}}>
                              <div style={{fontSize:13,fontWeight:800,color:alert?.triggered?C.red:C.textPri,fontFamily:FONT}}>${rack?.toFixed(4)}</div>
                              <div style={{fontSize:9,color:gsig?.trend3d>0?C.red:C.green,fontFamily:FONT}}>
                                {gsig?.trend3d>0?"":""}${Math.abs(gsig?.trend3d||0).toFixed(4)} 3d
                              </div>
                              {alert&&<div style={{fontSize:8.5,color:alert.triggered?C.red:C.textMut,fontWeight:700}}>{alert.triggered?"":""} ${alert.threshold}</div>}
                            </td>
                          );
                        })}
                        <td style={{padding:"10px 12px"}}>
                          {sig&&<span style={{fontSize:9.5,fontWeight:700,padding:"3px 8px",borderRadius:8,background:`${sig.color}18`,color:sig.color,border:`1px solid ${sig.color}40`,whiteSpace:"nowrap"}}>{sig.signal}</span>}
                        </td>
                        <td style={{padding:"10px 12px"}}>
                          <div style={{display:"flex",alignItems:"center",gap:6}}>
                            <Spark data={hist.slice(-14)} color={trend30>0?C.red:C.green} h={24}/>
                            <span style={{fontSize:10,fontWeight:700,color:trend30>0?C.red:C.green,fontFamily:FONT,whiteSpace:"nowrap"}}>{trend30>0?"+":""}{trend30.toFixed(4)}</span>
                          </div>
                        </td>
                        <td style={{padding:"10px 12px"}}>
                          <div style={{display:"flex",gap:5}}>
                            <button onClick={()=>{setNewPO(p=>({...p,terminal:t.id}));setShowPOModal(true);}}
                              style={{fontSize:9.5,padding:"4px 8px",borderRadius:5,border:`1px solid ${C.gold}`,background:darkMode?"rgba(200,164,74,.12)":"#FFF9E6",color:C.gold,fontWeight:700,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap"}}>
                              + PO
                            </button>
                            <button onClick={()=>{setProcTab("ai");runAISourcing("Regular",100000,t.id);}}
                              style={{fontSize:9.5,padding:"4px 8px",borderRadius:5,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,cursor:"pointer",fontFamily:FONT}}>
                              
                            </button>
                          </div>
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>

            {/* Alert manager */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}> Price Alert Rules</div>
              <table style={{width:"100%",borderCollapse:"collapse"}}>
                <thead>
                  <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                    {["Terminal","Grade","Type","Threshold","Status","Triggered","Note",""].map(h=>(
                      <th key={h} style={{padding:"7px 10px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT}}>{h}</th>
                    ))}
                  </tr>
                </thead>
                <tbody>
                  {alerts.map((a,ai)=>(
                    <tr key={a.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:a.triggered&&a.active?(darkMode?"rgba(239,68,68,.06)":"#FFF8F8"):"transparent"}}>
                      <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>{TERMINALS.find(t=>t.id===a.terminal)?.short}</td>
                      <td style={{padding:"8px 10px"}}><GradeTag grade={a.grade} darkMode={darkMode}/></td>
                      <td style={{padding:"8px 10px",fontSize:10.5,color:a.type==="ABOVE"?C.red:a.type==="BELOW"?C.green:C.amber,fontWeight:700}}>{a.type}</td>
                      <td style={{padding:"8px 10px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${a.threshold}</td>
                      <td style={{padding:"8px 10px"}}>
                        <button onClick={()=>setAlerts(prev=>prev.map((x,xi)=>xi===ai?{...x,active:!x.active}:x))}
                          style={{padding:"3px 10px",borderRadius:10,border:"none",background:a.active?(darkMode?"rgba(5,150,105,.15)":"#ECFDF5"):(darkMode?"rgba(100,116,139,.1)":"#F8FAFC"),color:a.active?"#059669":C.textMut,fontSize:10,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                          {a.active?"Active":"Off"}
                        </button>
                      </td>
                      <td style={{padding:"8px 10px"}}>
                        <span style={{fontSize:11,fontWeight:700,color:a.triggered&&a.active?C.red:C.textMut}}>{a.triggered&&a.active?" YES":"—"}</span>
                      </td>
                      <td style={{padding:"8px 10px",fontSize:10,color:C.textSec,maxWidth:220,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{a.note}</td>
                      <td style={{padding:"8px 10px"}}>
                        <button onClick={()=>setAlerts(prev=>prev.filter((_,xi)=>xi!==ai))}
                          style={{padding:"3px 8px",borderRadius:5,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textMut,fontSize:10,cursor:"pointer"}}></button>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
              <button onClick={()=>setAlerts(prev=>[...prev,{id:`al${Date.now()}`,terminal:"selma",grade:"Regular",type:"ABOVE",threshold:2.55,active:true,triggered:false,note:"New alert"}])}
                style={{marginTop:12,padding:"7px 16px",borderRadius:7,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:11,cursor:"pointer",fontFamily:FONT}}>
                + Add Alert Rule
              </button>
            </div>
          </div>
        )}

        {/*  PURCHASE ORDERS  */}
        {procTab==="po"&&(
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            <div style={{display:"flex",justifyContent:"flex-end"}}>
              <button onClick={()=>setShowPOModal(true)}
                style={{padding:"9px 20px",borderRadius:8,border:"none",background:C.gold,color:"#0D1B2A",fontSize:12,fontWeight:800,cursor:"pointer",fontFamily:FONT}}>
                + New Purchase Order
              </button>
            </div>

            {/* PO table */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,overflow:"hidden"}}>
              <table style={{width:"100%",borderCollapse:"collapse"}}>
                <thead>
                  <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                    {["PO #","Supplier","Terminal","Grade","Volume","$/gal","Total Cost","Status","Delivery","Invoiced","Notes",""].map(h=>(
                      <th key={h} style={{padding:"9px 12px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT,whiteSpace:"nowrap"}}>{h}</th>
                    ))}
                  </tr>
                </thead>
                <tbody>
                  {pos.map((po,pi)=>{
                    const supplier = SUPPLIERS.find(s=>s.id===po.supplierId);
                    const term = TERMINALS.find(t=>t.id===po.terminal);
                    return (
                      <tr key={po.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:po.isNew?(darkMode?"rgba(200,164,74,.06)":"#F8FAFB"):pi%2===0?"transparent":darkMode?"rgba(255,255,255,.015)":"rgba(0,0,0,.012)"}}>
                        <td style={{padding:"9px 12px",fontSize:11,fontWeight:800,color:C.gold,fontFamily:FONT,whiteSpace:"nowrap"}}>{po.id}</td>
                        <td style={{padding:"9px 12px",fontSize:11,fontWeight:600,color:C.textPri,fontFamily:FONT}}>{supplier?.short||"—"}</td>
                        <td style={{padding:"9px 12px",fontSize:11,color:C.textSec}}>{term?.short||"—"}</td>
                        <td style={{padding:"9px 12px"}}><GradeTag grade={po.grade} darkMode={darkMode}/></td>
                        <td style={{padding:"9px 12px",fontSize:11,fontFamily:FONT,color:C.textPri}}>{po.gals.toLocaleString()}</td>
                        <td style={{padding:"9px 12px",fontSize:11,fontFamily:FONT,color:C.textPri}}>${po.pricePerGal.toFixed(4)}</td>
                        <td style={{padding:"9px 12px",fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${po.totalCost.toLocaleString()}</td>
                        <td style={{padding:"9px 12px"}}>
                          <span style={{fontSize:9.5,fontWeight:700,padding:"3px 9px",borderRadius:8,background:poStatusBg(po.status),color:poStatusColor(po.status),border:`1px solid ${poStatusColor(po.status)}40`}}>{po.status}</span>
                        </td>
                        <td style={{padding:"9px 12px",fontSize:10.5,color:C.textSec,whiteSpace:"nowrap"}}>{po.delivery}</td>
                        <td style={{padding:"9px 12px",textAlign:"center",fontSize:12,color:po.invoiced?C.green:C.textMut}}>{po.invoiced?"":"—"}</td>
                        <td style={{padding:"9px 12px",fontSize:10,color:C.textSec,maxWidth:160,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{po.notes}</td>
                        <td style={{padding:"9px 12px"}}>
                          {po.status==="DRAFT"&&(
                            <button onClick={()=>setPos(prev=>prev.map(p=>p.id===po.id?{...p,status:"CONFIRMED"}:p))}
                              style={{fontSize:9.5,padding:"3px 10px",borderRadius:5,border:`1px solid #0891B2`,background:darkMode?"rgba(8,145,178,.12)":"#ECFEFF",color:"#0891B2",fontWeight:700,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap"}}>
                              Approve
                            </button>
                          )}
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>

            {/* Spend summary */}
            <div style={{display:"flex",gap:12}}>
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}>April Spend Summary</div>
                {[
                  {l:"Confirmed + Loading + Pending", v:`$${(pos.filter(p=>["CONFIRMED","LOADING","PENDING"].includes(p.status)).reduce((a,p)=>a+p.totalCost,0)).toLocaleString()}`, color:C.blue},
                  {l:"Draft (pending approval)",       v:`$${(pos.filter(p=>p.status==="DRAFT").reduce((a,p)=>a+p.totalCost,0)).toLocaleString()}`,   color:C.amber},
                  {l:"Delivered + invoiced",           v:`$${totalDelivered.toLocaleString()}`,                                                         color:C.green},
                  {l:"Total committed this cycle",     v:`$${totalCommitted.toLocaleString()}`,                                                         color:C.gold},
                ].map((row,ri)=>(
                  <div key={ri} style={{display:"flex",justifyContent:"space-between",padding:"7px 0",borderBottom:`1px solid ${C.cardBord}`}}>
                    <span style={{fontSize:10.5,color:C.textSec,fontFamily:FONT}}>{row.l}</span>
                    <span style={{fontSize:12,fontWeight:800,color:row.color,fontFamily:FONT}}>{row.v}</span>
                  </div>
                ))}
              </div>
              <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}>Supplier Concentration</div>
                {SUPPLIERS.slice(0,4).map((s,si)=>{
                  const spennd = pos.filter(p=>p.supplierId===s.id).reduce((a,p)=>a+p.totalCost,0);
                  const pct = totalCommitted>0?spennd/totalCommitted:0;
                  return (
                    <div key={s.id} style={{marginBottom:8}}>
                      <div style={{display:"flex",justifyContent:"space-between",marginBottom:3}}>
                        <span style={{fontSize:10.5,color:C.textPri,fontFamily:FONT}}>{s.short}</span>
                        <span style={{fontSize:10.5,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${(spennd/1000).toFixed(0)}K ({Math.round(pct*100)}%)</span>
                      </div>
                      <div style={{height:5,background:C.cardBord,borderRadius:2,overflow:"hidden"}}>
                        <div style={{height:"100%",width:`${pct*100}%`,background:si===0?C.gold:si===1?C.blue:si===2?"#059669":"#0D9488",borderRadius:2}}/>
                      </div>
                    </div>
                  );
                })}
              </div>
            </div>
          </div>
        )}

        {/*  LANDED COST CALCULATOR  */}
        {procTab==="landed"&&(()=>{
          const lc = calcLanded(lcSupp, lcTerm, lcGrade, lcGals);
          const stTaxAdj = lc?{...lc, stTax:STATE_TAX[lcDelivState]||0.385, landed:lc.contract+lc.tariff+lc.freight+(STATE_TAX[lcDelivState]||0.385)+FED_TAX, total:lcGals*(lc.contract+lc.tariff+lc.freight+(STATE_TAX[lcDelivState]||0.385)+FED_TAX)}:null;
          const spot = lc?{landed:lc.spotLanded, total:lcGals*lc.spotLanded}:null;
          const altBest = ALT_SUPPLY_POINTS.filter(sp=>sp.availableGrades.includes(lcGrade)).map(sp=>({...sp, lc:altLandedCost(sp,lcGrade,STATE_TAX[lcDelivState]||0.385)})).filter(sp=>sp.lc).sort((a,b)=>a.lc.spot-b.lc.spot)[0];
          const cheapest = [stTaxAdj?.landed, spot?.landed, altBest?.lc?.spot].filter(Boolean).reduce((a,b)=>a<b?a:b,999);

          return (
            <div style={{display:"flex",flexDirection:"column",gap:12}}>
              {/* Inputs */}
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:14}}> Landed Cost Calculator — Configure Your Order</div>
                <div style={{display:"flex",gap:14,flexWrap:"wrap",alignItems:"flex-end"}}>
                  {[
                    {label:"Supplier", el:<select value={lcSupp} onChange={e=>{setLcSupp(e.target.value);setLcTerm(SUPPLIERS.find(s=>s.id===e.target.value)?.terminals[0]||"selma");}} style={{padding:"7px 10px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textPri,fontSize:11,fontFamily:FONT,minWidth:160,cursor:"pointer"}}>{SUPPLIERS.map(s=><option key={s.id} value={s.id}>{s.name}</option>)}</select>},
                    {label:"Terminal", el:<select value={lcTerm} onChange={e=>setLcTerm(e.target.value)} style={{padding:"7px 10px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textPri,fontSize:11,fontFamily:FONT,cursor:"pointer"}}>{SUPPLIERS.find(s=>s.id===lcSupp)?.terminals.map(tid=><option key={tid} value={tid}>{TERMINALS.find(t=>t.id===tid)?.name}</option>)}</select>},
                    {label:"Grade",   el:<select value={lcGrade} onChange={e=>setLcGrade(e.target.value)} style={{padding:"7px 10px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textPri,fontSize:11,fontFamily:FONT,cursor:"pointer"}}>{GRADES.map(g=><option key={g} value={g}>{g}</option>)}</select>},
                    {label:"Delivery State", el:<select value={lcDelivState} onChange={e=>setLcDelivState(e.target.value)} style={{padding:"7px 10px",borderRadius:6,border:`1px solid ${C.cardBord}`,background:C.cardBg,color:C.textPri,fontSize:11,fontFamily:FONT,cursor:"pointer"}}>{Object.keys(STATE_TAX).map(st=><option key={st} value={st}>{st} (${STATE_TAX[st].toFixed(4)}/gal)</option>)}</select>},
                    {label:`Volume: ${(lcGals/1000).toFixed(0)}K gal`, el:<input type="range" min={10000} max={250000} step={5000} value={lcGals} onChange={e=>setLcGals(+e.target.value)} style={{width:160,accentColor:C.gold}}/>},
                  ].map((item,ii)=>(
                    <div key={ii}>
                      <div style={{fontSize:9.5,color:C.textMut,textTransform:"uppercase",letterSpacing:.5,marginBottom:5,fontFamily:FONT}}>{item.label}</div>
                      {item.el}
                    </div>
                  ))}
                  <button onClick={()=>{setNewPO(p=>({...p,supplierId:lcSupp,terminal:lcTerm,grade:lcGrade,gals:lcGals}));setShowPOModal(true);}}
                    style={{padding:"9px 18px",borderRadius:8,border:"none",background:C.gold,color:"#0D1B2A",fontSize:11,fontWeight:700,cursor:"pointer",fontFamily:FONT,whiteSpace:"nowrap",height:36}}>
                    → Create PO
                  </button>
                </div>
              </div>

              {stTaxAdj&&(
                <div style={{display:"flex",gap:12}}>
                  {/* Cost stack breakdown */}
                  <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                    <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:14}}>Cost Breakdown — Contract Path</div>
                    {[
                      {label:"Rack Price",      val:lc.rack,      color:"#0891B2", pct:lc.rack/stTaxAdj.landed},
                      {label:"Contract Diff",   val:lc.diff,      color:C.gold,    pct:lc.diff/stTaxAdj.landed},
                      {label:"Pipeline Tariff", val:lc.tariff,    color:"#0D9488", pct:lc.tariff/stTaxAdj.landed},
                      {label:"Freight",         val:lc.freight,   color:"#EA580C", pct:lc.freight/stTaxAdj.landed},
                      {label:`${lcDelivState} State Tax`, val:stTaxAdj.stTax, color:"#059669", pct:stTaxAdj.stTax/stTaxAdj.landed},
                      {label:"Federal Excise",  val:FED_TAX,      color:"#64748B", pct:FED_TAX/stTaxAdj.landed},
                    ].map((seg,si)=>(
                      <div key={si} style={{marginBottom:8}}>
                        <div style={{display:"flex",justifyContent:"space-between",marginBottom:3,alignItems:"center"}}>
                          <div style={{display:"flex",alignItems:"center",gap:7}}>
                            <div style={{width:10,height:10,borderRadius:2,background:seg.color,flexShrink:0}}/>
                            <span style={{fontSize:10.5,color:C.textSec,fontFamily:FONT}}>{seg.label}</span>
                          </div>
                          <span style={{fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${seg.val.toFixed(4)}</span>
                        </div>
                        <div style={{height:5,background:C.cardBord,borderRadius:2,overflow:"hidden"}}>
                          <div style={{height:"100%",width:`${seg.pct*100}%`,background:seg.color,borderRadius:2}}/>
                        </div>
                      </div>
                    ))}
                    <div style={{borderTop:`2px solid ${C.cardBord}`,paddingTop:10,display:"flex",justifyContent:"space-between",alignItems:"center",marginTop:4}}>
                      <span style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT}}>Total Landed Cost</span>
                      <div style={{textAlign:"right"}}>
                        <div style={{fontSize:22,fontWeight:900,color:stTaxAdj.landed===cheapest?C.green:C.textPri,fontFamily:FONT}}>${stTaxAdj.landed.toFixed(4)}/gal</div>
                        <div style={{fontSize:12,color:C.textSec,fontFamily:FONT}}>${stTaxAdj.total.toLocaleString()} total</div>
                      </div>
                    </div>
                  </div>

                  {/* Comparison: contract vs spot vs alt */}
                  <div style={{flex:1,background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
                    <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:14}}>Source Comparison — {(lcGals/1000).toFixed(0)}K gal</div>
                    {[
                      {label:"Contract Path",       val:stTaxAdj.landed,   total:stTaxAdj.total,    source:`${SUPPLIERS.find(s=>s.id===lcSupp)?.short} at ${TERMINALS.find(t=>t.id===lcTerm)?.short}`},
                      {label:"Spot Market",         val:spot?.landed||0,   total:spot?.total||0,    source:"Open market at same terminal"},
                      ...(altBest?[{label:`${altBest.name}`, val:altBest.lc.spot||0, total:(altBest.lc.spot||0)*lcGals, source:`${altBest.type} · ${altBest.leadDays}d lead`}]:[]),
                    ].map((opt,oi)=>{
                      const isBest = Math.abs(opt.val - cheapest)<0.0001;
                      const vsBest = opt.val - cheapest;
                      return (
                        <div key={oi} style={{padding:"12px 14px",borderRadius:9,marginBottom:8,border:`2px solid ${isBest?C.green:C.cardBord}`,background:isBest?(darkMode?"rgba(5,150,105,.08)":"#F0FDF4"):(darkMode?"rgba(255,255,255,.02)":"#FAFAFA")}}>
                          <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:4}}>
                            <div>
                              <div style={{fontSize:11,fontWeight:700,color:isBest?C.green:C.textPri,fontFamily:FONT}}>{opt.label} {isBest&&" BEST"}</div>
                              <div style={{fontSize:9.5,color:C.textMut}}>{opt.source}</div>
                            </div>
                            <div style={{textAlign:"right"}}>
                              <div style={{fontSize:18,fontWeight:900,color:isBest?C.green:C.textPri,fontFamily:FONT}}>${opt.val.toFixed(4)}</div>
                              <div style={{fontSize:10,color:C.textSec}}>total: ${opt.total.toLocaleString()}</div>
                            </div>
                          </div>
                          {!isBest&&vsBest>0&&<div style={{fontSize:10,color:C.red,fontWeight:700}}>+${vsBest.toFixed(4)}/gal · +${(vsBest*lcGals).toFixed(0)} total vs best</div>}
                        </div>
                      );
                    })}

                    {/* Dispatch link */}
                    <div style={{marginTop:12,padding:"10px 12px",borderRadius:8,background:darkMode?"rgba(200,164,74,.08)":"#F8FAFB",border:`1px solid ${C.gold}30`}}>
                      <div style={{fontSize:10.5,fontWeight:700,color:C.gold,marginBottom:4}}> Transport cost included</div>
                      <div style={{fontSize:10,color:C.textSec,lineHeight:1.5}}>Freight of ${lc.freight.toFixed(4)}/gal in landed cost = ${(lc.freight*lcGals).toLocaleString()} on this order. Cheaper terminal may offset higher freight — use the Rack Prices tab to compare cross-terminal landed costs including dispatch.</div>
                    </div>
                  </div>
                </div>
              )}
            </div>
          );
        })()}

        {/*  AI SOURCING (Phase 2)  */}
        {procTab==="ai"&&(
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            {/* Phase badge */}
            <div style={{background:darkMode?"rgba(13,148,136,.1)":"#F0FDFA",border:`1px solid #0D948840`,borderRadius:10,padding:"12px 16px",display:"flex",alignItems:"center",gap:14}}>
              <div style={{width:40,height:40,borderRadius:10,background:"linear-gradient(135deg,#0D9488,#9333EA)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:20}}></div>
              <div>
                <div style={{display:"flex",alignItems:"center",gap:8}}>
                  <span style={{fontSize:13,fontWeight:800,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:FONT}}>AI Sourcing Recommendations</span>
                  <span style={{fontSize:9,fontWeight:700,padding:"2px 7px",borderRadius:5,background:"#0D9488",color:"#fff"}}>Phase 2</span>
                </div>
                <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",marginTop:2}}>Analyzes all suppliers, rack trends, forecast, hedging, Colonial constraints, and alternative sources to recommend the optimal buy strategy.</div>
              </div>
            </div>

            {/* Quick launch buttons */}
            <div style={{display:"flex",gap:8,flexWrap:"wrap"}}>
              {TERMINALS.slice(0,4).map(t=>
                GRADES.map(g=>(
                  <button key={`${t.id}-${g}`} onClick={()=>runAISourcing(g,100000,t.id)}
                    style={{padding:"7px 14px",borderRadius:7,border:`1px solid ${C.cardBord}`,background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC",color:C.textSec,fontSize:10.5,cursor:"pointer",fontFamily:FONT,display:"flex",alignItems:"center",gap:5}}>
                    <ZoneBadge terminalId={t.id}/>{t.short} {g}
                  </button>
                ))
              )}
            </div>

            {/* Result */}
            {aiSourcingLoading&&(
              <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:"30px",textAlign:"center"}}>
                <div style={{fontSize:28,marginBottom:8}}></div>
                <div style={{fontSize:13,color:C.textSec}}>Analyzing suppliers, price trends, pipeline status, and alternative sources...</div>
              </div>
            )}

            {aiSourcingResult&&!aiSourcingResult.error&&(
              <div style={{background:C.cardBg,border:`2px solid #0D9488`,borderRadius:10,padding:20}}>
                <div style={{display:"flex",alignItems:"flex-start",justifyContent:"space-between",marginBottom:16,gap:12}}>
                  <div>
                    <div style={{fontSize:10,fontWeight:700,color:"#0D9488",textTransform:"uppercase",letterSpacing:.6,marginBottom:6}}>AI Recommendation — {aiSourcingResult.grade} at {TERMINALS.find(t=>t.id===aiSourcingResult.terminal)?.name}</div>
                    <div style={{fontSize:18,fontWeight:900,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:FONT,marginBottom:4}}>{aiSourcingResult.recommendedSupplier}</div>
                    <div style={{display:"flex",gap:10,flexWrap:"wrap",marginBottom:8}}>
                      {[
                        {l:"Source",  v:aiSourcingResult.recommendedSource,  color:"#0D9488"},
                        {l:"Timing",  v:aiSourcingResult.recommendedTiming,  color:aiSourcingResult.recommendedTiming?.includes("now")?C.green:C.amber},
                        {l:"Landed",  v:`$${aiSourcingResult.landedCost?.toFixed(4)}/gal`, color:C.textPri},
                      ].map((s,si)=>(
                        <div key={si} style={{padding:"4px 10px",borderRadius:7,background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC",border:`1px solid ${C.cardBord}`}}>
                          <span style={{fontSize:9,color:C.textMut,textTransform:"uppercase",letterSpacing:.4}}>{s.l}: </span>
                          <span style={{fontSize:11,fontWeight:700,color:s.color,fontFamily:FONT}}>{s.v}</span>
                        </div>
                      ))}
                      {aiSourcingResult.potentialSavings&&(
                        <div style={{padding:"4px 10px",borderRadius:7,background:darkMode?"rgba(5,150,105,.12)":"#ECFDF5",border:`1px solid #05965040`}}>
                          <span style={{fontSize:9,color:C.textMut,textTransform:"uppercase",letterSpacing:.4}}>Savings: </span>
                          <span style={{fontSize:11,fontWeight:700,color:C.green,fontFamily:FONT}}>${aiSourcingResult.potentialSavings?.toLocaleString()}</span>
                        </div>
                      )}
                    </div>
                    <div style={{fontSize:11,color:C.textSec,lineHeight:1.6,marginBottom:8}}>{aiSourcingResult.reasoning}</div>
                    {aiSourcingResult.riskNote&&<div style={{fontSize:10.5,color:C.amber,display:"flex",gap:6}}><span></span>{aiSourcingResult.riskNote}</div>}
                    {aiSourcingResult.hedgeSuggestion&&<div style={{fontSize:10.5,color:"#0D9488",marginTop:4,display:"flex",gap:6}}><span></span>{aiSourcingResult.hedgeSuggestion}</div>}
                  </div>
                </div>
                <div style={{display:"flex",gap:8}}>
                  <button onClick={()=>{const s=SUPPLIERS.find(sup=>sup.name.includes(aiSourcingResult.recommendedSupplier?.split(" ")[0]));if(s){setNewPO(p=>({...p,supplierId:s.id,terminal:aiSourcingResult.terminal,grade:aiSourcingResult.grade,gals:aiSourcingResult.vol}));setShowPOModal(true);}}}
                    style={{padding:"9px 20px",borderRadius:8,border:"none",background:C.gold,color:"#0D1B2A",fontSize:12,fontWeight:700,cursor:"pointer",fontFamily:FONT}}>
                    → Create PO from Recommendation
                  </button>
                  <button onClick={()=>setAiSourcingResult(null)} style={{padding:"9px 16px",borderRadius:8,border:`1px solid ${C.cardBord}`,background:"transparent",color:C.textSec,fontSize:11,cursor:"pointer",fontFamily:FONT}}>
                    Clear
                  </button>
                </div>
              </div>
            )}
            {aiSourcingResult?.error&&<div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:20,fontSize:11,color:C.textSec}}>{aiSourcingResult.error}</div>}
          </div>
        )}

        {/*  HEDGING (Phase 2)  */}
        {procTab==="hedging"&&(
          <div style={{display:"flex",flexDirection:"column",gap:12}}>
            <div style={{background:darkMode?"rgba(13,148,136,.1)":"#F0FDFA",border:`1px solid #0D948840`,borderRadius:10,padding:"12px 16px",display:"flex",alignItems:"center",gap:12}}>
              <div style={{width:36,height:36,borderRadius:8,background:"linear-gradient(135deg,#0D9488,#9333EA)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:18}}></div>
              <div>
                <div style={{display:"flex",alignItems:"center",gap:8}}>
                  <span style={{fontSize:13,fontWeight:800,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:FONT}}>Hedging & Risk Management</span>
                  <span style={{fontSize:9,fontWeight:700,padding:"2px 7px",borderRadius:5,background:"#0D9488",color:"#fff"}}>Phase 2</span>
                </div>
                <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",marginTop:2}}>ULSD/RBOB swaps, caps, and collars. Full P&L mark-to-market and hedge ratio optimization coming in Phase 2.</div>
              </div>
            </div>

            {/* Existing positions */}
            <div style={{background:C.cardBg,border:`1px solid ${C.cardBord}`,borderRadius:10,padding:16}}>
              <div style={{fontSize:12,fontWeight:700,color:C.textPri,fontFamily:FONT,marginBottom:12}}>Current Hedge Positions</div>
              <table style={{width:"100%",borderCollapse:"collapse"}}>
                <thead>
                  <tr style={{background:darkMode?"rgba(255,255,255,.04)":"#F8FAFC"}}>
                    {["ID","Type","Commodity","Volume","Strike","Expiry","MTM P&L","Status","Counterparty"].map(h=>(
                      <th key={h} style={{padding:"8px 12px",fontSize:9,color:C.textMut,fontWeight:700,textAlign:"left",textTransform:"uppercase",letterSpacing:.4,borderBottom:`1px solid ${C.cardBord}`,fontFamily:FONT}}>{h}</th>
                    ))}
                  </tr>
                </thead>
                <tbody>
                  {HEDGE_POSITIONS.map((h,hi)=>(
                    <tr key={h.id} style={{borderBottom:`1px solid ${C.cardBord}`,background:h.status==="EXPIRING"?(darkMode?"rgba(251,191,36,.06)":"#F8FAFB"):"transparent"}}>
                      <td style={{padding:"9px 12px",fontSize:10.5,fontWeight:700,color:C.gold,fontFamily:FONT}}>{h.id}</td>
                      <td style={{padding:"9px 12px",fontSize:10.5,fontWeight:700,color:"#0D9488"}}>{h.type}</td>
                      <td style={{padding:"9px 12px",fontSize:10.5,color:C.textPri}}>{h.commodity}</td>
                      <td style={{padding:"9px 12px",fontSize:11,color:C.textPri,fontFamily:FONT}}>{(h.volume/1000).toFixed(0)}K gal</td>
                      <td style={{padding:"9px 12px",fontSize:11,fontWeight:700,color:C.textPri,fontFamily:FONT}}>${h.strike.toFixed(4)}</td>
                      <td style={{padding:"9px 12px",fontSize:10.5,color:h.status==="EXPIRING"?C.amber:C.textSec,fontWeight:h.status==="EXPIRING"?700:400}}>{h.expiry}</td>
                      <td style={{padding:"9px 12px",fontSize:12,fontWeight:800,color:h.mtm>0?C.green:C.red,fontFamily:FONT}}>{h.mtm>0?"+":""}{h.mtm.toLocaleString()}</td>
                      <td style={{padding:"9px 12px"}}>
                        <span style={{fontSize:9.5,fontWeight:700,padding:"2px 8px",borderRadius:8,background:h.status==="EXPIRING"?(darkMode?"rgba(251,191,36,.15)":"#F8FAFB"):darkMode?"rgba(5,150,105,.12)":"#ECFDF5",color:h.status==="EXPIRING"?C.amber:"#059669",border:`1px solid ${h.status==="EXPIRING"?C.amber+"40":"#05965040"}`}}>{h.status}</span>
                      </td>
                      <td style={{padding:"9px 12px",fontSize:10.5,color:C.textSec}}>{h.counterparty}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
              <div style={{marginTop:12,padding:"10px 14px",borderRadius:8,background:darkMode?"rgba(200,164,74,.08)":"#F8FAFB",border:`1px solid ${C.gold}30`,display:"flex",justifyContent:"space-between",alignItems:"center"}}>
                <div>
                  <div style={{fontSize:11,fontWeight:700,color:C.gold}}>Total MTM P&L</div>
                  <div style={{fontSize:10,color:C.textSec,marginTop:2}}>Mark-to-market on all open positions</div>
                </div>
                <div style={{fontSize:22,fontWeight:900,color:C.green,fontFamily:FONT}}>+${HEDGE_POSITIONS.reduce((a,h)=>a+h.mtm,0).toLocaleString()}</div>
              </div>
            </div>
          </div>
        )}

      </div>
    );
  };

  //  Ticker items string 
  const tickerStr = TICKER_ITEMS.map(t => `${t.label}: ${t.val}  ${t.up?"":""} ${t.delta}`).join(" ·     ");
  const tickerDbl = tickerStr + " ·     " + tickerStr;

  const SIDEBAR_W = sidebarExpanded ? 200 : 56;
  const invAlertCount = STORES.filter(s=>GRADES.some(g=>s.daysSupply[g]<1.5)).length;

  return (
    <div style={{ fontFamily:"Arial,sans-serif", background:C.bodyBg, minHeight:"100vh", color:C.textPri, display:"flex", flexDirection:"column" }}>

      {/*  TOP BAR  */}
      <div style={{ position:"fixed", top:0, left:0, right:0, zIndex:200, background:C.navBg, borderBottom:`1px solid ${C.navBorder}`, height:48, display:"flex", alignItems:"center", padding:"0 16px", gap:12 }}>
        {/* Logo — Opportune brand mark + FuelOps wordmark */}
        <div style={{ display:"flex", alignItems:"center", gap:10, width:sidebarExpanded?184:56, transition:"width .2s", overflow:"hidden", flexShrink:0 }}>
          <img src={OPPORTUNE_LOGO} alt="Opportune" style={{ height:32, width:"auto", flexShrink:0, display:"block" }}/>
          {sidebarExpanded && (
            <div style={{ overflow:"hidden" }}>
              <div style={{ fontSize:14, fontWeight:800, color:"#E8EDF6", letterSpacing:-0.3, whiteSpace:"nowrap" }}>FuelOps</div>
            </div>
          )}
        </div>

        {/* Ticker */}
        <div style={{ flex:1, height:"100%", overflow:"hidden", position:"relative" }}>
          <div style={{ display:"flex", alignItems:"center", height:"100%", position:"absolute", whiteSpace:"nowrap",
            transform:`translateX(-${tickerPos % (tickerDbl.length * 5.6)}px)`, transition:"none" }}>
            {[...Array(3)].map((_, ci) => (
              <span key={ci} style={{ fontFamily:"Arial,sans-serif", fontSize:10.5 }}>
                {TICKER_ITEMS.map((item, ii) => (
                  <span key={ii}>
                    <span style={{ color:"#3D5070", margin:"0 12px" }}>·</span>
                    <span style={{ color:"#7B8FAF", marginRight:4 }}>{item.label}:</span>
                    <span style={{ color:"#E8EDF6", fontWeight:700, marginRight:4 }}>{item.val}</span>
                    <span style={{ color:item.up?"#22C55E":"#F87171", fontWeight:700 }}>{item.up?"":""} {item.delta}</span>
                  </span>
                ))}
              </span>
            ))}
          </div>
        </div>

        {/* Right controls */}
        <div style={{ display:"flex", alignItems:"center", gap:10, flexShrink:0 }}>
          <div style={{ fontSize:10.5, color:"#7B8FAF" }}>Apr 22, 2026 · 08:30 CT</div>
          <button onClick={()=>setDarkMode(d=>!d)}
            style={{ padding:"5px 12px", borderRadius:6, border:"1px solid #1E2433", background:"rgba(255,255,255,.05)", color:"#F4D398", fontSize:11, cursor:"pointer", fontFamily:"Arial,sans-serif" }}>
            {darkMode?" Light":" Dark"}
          </button>
        </div>
      </div>

      {/*  MAIN AREA (below top bar)  */}
      <div style={{ display:"flex", paddingTop:48, minHeight:"100vh" }}>

        {/*  LEFT SIDEBAR  */}
        <div style={{
          position:"fixed", top:48, left:0, bottom:0, zIndex:100,
          width:SIDEBAR_W, transition:"width .2s ease",
          background:C.navBg, borderRight:`1px solid ${C.navBorder}`,
          display:"flex", flexDirection:"column", overflow:"hidden",
        }}>
          {/* Collapse toggle */}
          <button onClick={()=>setSidebarExpanded(e=>!e)}
            style={{ display:"flex", alignItems:"center", justifyContent:sidebarExpanded?"flex-end":"center", padding:"10px 12px", background:"none", border:"none", borderBottom:`1px solid ${C.navBorder}`, cursor:"pointer", color:"#7B8FAF", fontSize:14, flexShrink:0 }}>
            {sidebarExpanded ? "" : ""}
          </button>

          {/* Nav items */}
          <div style={{ flex:1, padding:"8px 0", overflowY:"auto", overflowX:"hidden" }}>
            {TABS.map((tab,idx)=>{
              const isActive = activeTab === tab.id;
              const badge = tab.id==="inventory" ? invAlertCount : tab.id==="orders" ? pendingOrders : 0;
              const prevSection = idx > 0 ? TABS[idx-1].section : null;
              const isFirstOfSection = tab.section && tab.section !== prevSection;
              return (
                <React.Fragment key={tab.id}>
                  {/* Section heading — expanded sidebar only */}
                  {isFirstOfSection && sidebarExpanded && (
                    <div style={{
                      padding: idx===0 ? "4px 16px 6px" : "14px 16px 6px",
                      fontSize:9.5, fontWeight:800, letterSpacing:1.3,
                      textTransform:"uppercase",
                      color:"#556B87", fontFamily:"Arial,sans-serif",
                      borderTop: idx > 0 ? `1px solid ${C.navBorder}` : "none",
                      marginTop: idx > 0 ? 6 : 0,
                    }}>
                      {tab.section}
                    </div>
                  )}
                  {/* Collapsed sidebar: just a thin separator */}
                  {isFirstOfSection && !sidebarExpanded && idx > 0 && (
                    <div style={{ height:1, background:C.navBorder, margin:"6px 14px" }}/>
                  )}
                  <button onClick={()=>setActiveTab(tab.id)}
                    title={!sidebarExpanded ? `${tab.label} — ${tab.subtitle}` : undefined}
                    style={{
                      display:"flex", alignItems:"center", gap:10,
                      width:"100%", padding:sidebarExpanded?"10px 16px":"10px 0",
                      justifyContent:sidebarExpanded?"flex-start":"center",
                      border:"none", cursor:"pointer",
                      background:isActive?"rgba(200,164,74,.12)":"transparent",
                      borderLeft:isActive?"3px solid #F4D398":"3px solid transparent",
                      color:isActive?"#F4D398":"#7B8FAF",
                      fontSize:13, fontWeight:isActive?700:400,
                      transition:"all .15s", fontFamily:"Arial,sans-serif",
                      whiteSpace:"nowrap", overflow:"hidden",
                      position:"relative",
                    }}>
                    {sidebarExpanded && (
                      <span style={{ flex:1, textAlign:"left", overflow:"hidden" }}>
                        <div style={{ fontSize:13, fontWeight:isActive?700:500, lineHeight:1.2 }}>{tab.label}</div>
                        <div style={{ fontSize:10, color:isActive?"rgba(200,164,74,.75)":"#4A5E7A", marginTop:2, fontWeight:400, lineHeight:1.2, overflow:"hidden", textOverflow:"ellipsis" }}>
                          {tab.subtitle}
                        </div>
                      </span>
                    )}
                    {badge > 0 && sidebarExpanded && (
                      <span style={{ fontSize:9, background:tab.id==="inventory"?"#EF4444":"#3B82F6", color:"#fff", borderRadius:10, padding:"1px 6px", fontWeight:700, flexShrink:0 }}>{badge}</span>
                    )}
                    {badge > 0 && !sidebarExpanded && (
                      <span style={{ position:"absolute", top:6, right:8, width:7, height:7, borderRadius:"50%", background:tab.id==="inventory"?"#EF4444":"#3B82F6" }}/>
                    )}
                  </button>
                </React.Fragment>
              );
            })}
          </div>

          {/* Bottom info */}
          {sidebarExpanded && (
            <div style={{ padding:"12px 16px", borderTop:`1px solid ${C.navBorder}`, flexShrink:0 }}>
              <div style={{ fontSize:9.5, color:"#3D5070", textTransform:"uppercase", letterSpacing:.6, marginBottom:4 }}>Market Status</div>
              <div style={{ display:"flex", alignItems:"center", gap:6 }}>
                <div style={{ width:7, height:7, borderRadius:"50%", background:"#22C55E" }}/>
                <span style={{ fontSize:10.5, color:"#7B8FAF" }}>Colonial Live</span>
              </div>
              <div style={{ display:"flex", alignItems:"center", gap:6, marginTop:4 }}>
                <div style={{ width:7, height:7, borderRadius:"50%", background:"#22C55E" }}/>
                <span style={{ fontSize:10.5, color:"#7B8FAF" }}>OPIS Feed Active</span>
              </div>
              <div style={{ fontSize:9, color:"#3D5070", marginTop:8 }}>Last refresh: 08:28 CT</div>
            </div>
          )}
        </div>

        {/*  CONTENT  */}
        <div style={{ marginLeft:SIDEBAR_W, transition:"margin-left .2s ease", flex:1, padding:"18px 20px", minWidth:0 }}>
          {/* Page-level title + subtitle + optional source-of-nav crumb */}
          <PageHeader
            title={TAB_BY_ID[activeTab]?.label || "Dashboard"}
            subtitle={TAB_BY_ID[activeTab]?.subtitle}
            crumb={dispatchCrumb}
            onClearCrumb={dispatchCrumb ? ()=>setDispatchCrumb(null) : null}
            C={C} darkMode={darkMode}
            right={
              <button onClick={()=>setTourStep(1)}
                title="Take a guided tour"
                style={{
                  padding:"3px 8px", borderRadius:5,
                  border:`1px solid ${C.cardBord}`,
                  background:"transparent",
                  color:C.textMut, fontSize:9.5, fontWeight:600,
                  cursor:"pointer", fontFamily:"Arial,sans-serif",
                  display:"flex", alignItems:"center", gap:4,
                  whiteSpace:"nowrap",
                }}>
                ◆ Tour
              </button>
            }
          />
          <div data-tour={activeTab}>
            {renderTab()}
          </div>
        </div>
      </div>

      {/* Guided walkthrough — rendered on top of everything when active */}
      {tourStep > 0 && (
        <TourOverlay step={tourStep} setStep={setTourStep}
          setActiveTab={setActiveTab} darkMode={darkMode}/>
      )}

      {/*  Toast notifications  */}
      <div style={{position:"fixed",bottom:90,left:"50%",transform:"translateX(-50%)",zIndex:1000,display:"flex",flexDirection:"column",gap:8,pointerEvents:"none"}}>
        {toasts.map(t=>(
          <div key={t.id} style={{padding:"10px 20px",borderRadius:10,background:t.type==="warn"?(darkMode?"rgba(251,191,36,.95)":"#FBBF24"):darkMode?"rgba(34,197,94,.95)":"#16A34A",color:"#fff",fontSize:12,fontWeight:700,fontFamily:"Arial,sans-serif",boxShadow:"0 4px 20px rgba(0,0,0,.3)",whiteSpace:"nowrap",animation:"fadeIn .2s ease"}}>
            {t.msg}
          </div>
        ))}
      </div>

      {/*  Dispatch Modal  */}
      {showDispatchModal&&dispatchTarget&&(
        <div style={{position:"fixed",inset:0,zIndex:800,background:"rgba(0,0,0,.6)",display:"flex",alignItems:"center",justifyContent:"center",padding:20}}
          onClick={e=>{if(e.target===e.currentTarget){setShowDispatchModal(false);setDispatchTarget(null);setAiDispatchResult(null);setDispatchCrumb(null);}}}>
          <div style={{background:darkMode?"#0F1420":"#fff",borderRadius:14,border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,width:520,maxHeight:"90vh",overflowY:"auto",boxShadow:"0 24px 80px rgba(0,0,0,.45)",display:"flex",flexDirection:"column"}}>

            {/* Header */}
            <div style={{padding:"16px 20px",borderBottom:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0}}>
              <div style={{flex:1,minWidth:0}}>
                {/* Source-of-navigation crumb (set when alert opened the modal) */}
                {dispatchCrumb && (
                  <div style={{
                    display:"inline-flex", alignItems:"center", gap:6,
                    padding:"3px 9px", borderRadius:12, marginBottom:7,
                    background: darkMode ? "rgba(200,164,74,.12)" : "#FFF9E6",
                    border: `1px solid ${darkMode ? "rgba(200,164,74,.35)" : "#F1D98F"}`,
                    fontSize:10, color: darkMode ? "#F4D398" : "#8B6914",
                    fontFamily:"Arial,sans-serif",
                  }}>
                    <span style={{ fontSize:8.5, fontWeight:800, letterSpacing:.6, textTransform:"uppercase", opacity:.8 }}>From</span>
                    <span style={{ fontWeight:600 }}>{dispatchCrumb}</span>
                  </div>
                )}
                <div style={{fontSize:15,fontWeight:800,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:"Arial,sans-serif"}}>Dispatch Load</div>
                <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",marginTop:2,fontFamily:"Arial,sans-serif",display:"flex",alignItems:"center",gap:6,flexWrap:"wrap"}}>
                  <span>{dispatchTarget.storeName} · {dispatchTarget.grade} · {(dispatchTarget.vol||0).toLocaleString()} gal · {TERMINALS.find(t=>t.id===dispatchTarget.terminal)?.short}</span>
                  {dispatchTarget.supplierShort && (
                    <span title={`${dispatchTarget.supplierName} · ${dispatchTarget.contractStatus}`} style={{
                      fontSize:9, fontWeight:800,
                      color: dispatchTarget.isSpot ? "#EA580C"
                            : dispatchTarget.contractStatus === "primary" ? "#16A34A"
                            : "#F4D398",
                      background: dispatchTarget.isSpot ? (darkMode?"rgba(234,88,12,.12)":"#FFF7ED")
                            : dispatchTarget.contractStatus === "primary" ? (darkMode?"rgba(22,163,74,.12)":"#F0FDF4")
                            : (darkMode?"rgba(200,164,74,.12)":"#F8FAFB"),
                      padding:"2px 7px", borderRadius:4, letterSpacing:.4,
                      border:`1px solid ${dispatchTarget.isSpot ? "#EA580C" : dispatchTarget.contractStatus === "primary" ? "#16A34A" : "#F4D398"}40`,
                    }}>
                      {dispatchTarget.supplierShort}{dispatchTarget.isSpot ? " · SPOT" : dispatchTarget.contractStatus === "secondary" ? " · 2°" : ""}
                    </span>
                  )}
                </div>
              </div>
              <button onClick={()=>{setShowDispatchModal(false);setDispatchTarget(null);setAiDispatchResult(null);setDispatchCrumb(null);}}
                style={{width:28,height:28,borderRadius:"50%",border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,background:"transparent",color:darkMode?"#7B8FAF":"#4A5E7A",fontSize:16,cursor:"pointer",display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0}}>×</button>
            </div>

            <div style={{padding:"16px 20px",display:"flex",flexDirection:"column",gap:16,overflowY:"auto"}}>

              {/*  SCHEDULE SECTION  */}
              <div style={{background:darkMode?"rgba(255,255,255,.03)":"#F8FAFC",borderRadius:10,padding:"14px 16px",border:`1px solid ${darkMode?"#1E2840":"#E2E8F0"}`}}>
                <div style={{fontSize:10.5,fontWeight:700,color:darkMode?"#7B8FAF":"#4A5E7A",textTransform:"uppercase",letterSpacing:.6,fontFamily:"Arial,sans-serif",marginBottom:12}}> Schedule</div>

                {/* Quick date buttons */}
                <div style={{display:"flex",gap:6,marginBottom:10}}>
                  {[
                    {label:"Today",     date:"2025-04-18"},
                    {label:"Tomorrow",  date:"2025-04-19"},
                    {label:"Wed Apr 16",date:"2025-04-18"},
                    {label:"Thu Apr 17",date:"2025-04-19"},
                  ].map(btn=>(
                    <button key={btn.date} onClick={()=>{setScheduleDate(btn.date);setAiDispatchResult(null);}}
                      style={{padding:"5px 10px",borderRadius:6,border:`1.5px solid ${scheduleDate===btn.date?"#F4D398":darkMode?"#1E2840":"#DDE3EC"}`,background:scheduleDate===btn.date?(darkMode?"rgba(200,164,74,.15)":"#FFF9E6"):"transparent",color:scheduleDate===btn.date?"#F4D398":darkMode?"#7B8FAF":"#4A5E7A",fontSize:10.5,fontWeight:scheduleDate===btn.date?700:400,cursor:"pointer",fontFamily:"Arial,sans-serif",whiteSpace:"nowrap"}}>
                      {btn.label}
                    </button>
                  ))}
                  <input type="date" value={scheduleDate} min="2025-04-18" max="2025-04-28" onChange={e=>{setScheduleDate(e.target.value);setAiDispatchResult(null);}}
                    style={{padding:"4px 8px",borderRadius:6,border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,background:darkMode?"#0D1B2A":"#fff",color:darkMode?"#E8EDF6":"#0D1B2A",fontSize:10.5,cursor:"pointer",fontFamily:"Arial,sans-serif"}}/>
                </div>

                {/* Time picker */}
                <div style={{display:"flex",alignItems:"center",gap:10}}>
                  <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",fontFamily:"Arial,sans-serif",whiteSpace:"nowrap"}}>Departure time:</div>
                  <input type="time" value={scheduleTime} onChange={e=>{setScheduleTime(e.target.value);setAiDispatchResult(null);}}
                    style={{padding:"5px 10px",borderRadius:6,border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,background:darkMode?"#0D1B2A":"#fff",color:darkMode?"#E8EDF6":"#0D1B2A",fontSize:11,fontFamily:"Arial,sans-serif"}}/>
                  <div style={{display:"flex",gap:5}}>
                    {["06:00","08:00","10:00","12:00","14:00"].map(t=>(
                      <button key={t} onClick={()=>{setScheduleTime(t);setAiDispatchResult(null);}}
                        style={{padding:"4px 8px",borderRadius:5,border:`1px solid ${scheduleTime===t?"#F4D398":darkMode?"#1E2840":"#DDE3EC"}`,background:scheduleTime===t?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):"transparent",color:scheduleTime===t?"#F4D398":darkMode?"#7B8FAF":"#4A5E7A",fontSize:9.5,cursor:"pointer",fontFamily:"Arial,sans-serif"}}>
                        {t}
                      </button>
                    ))}
                  </div>
                </div>

                {/* Schedule context checks */}
                {(()=>{
                  const daysOut = Math.round((new Date(scheduleDate)-new Date("2025-04-18"))/(1000*60*60*24));
                  const depletion = DEPLETION.find(d=>d.storeId===dispatchTarget.storeId);
                  const pipeWin   = COLONIAL.terminalWindows[dispatchTarget.terminal||"selma"];
                  const termStat  = TERMINAL_STATUS[dispatchTarget.terminal||"selma"];
                  const storeOk   = daysOut <= (depletion?.minCritical||99);
                  const winOpen   = (pipeWin?.daysToWindow||0) <= daysOut;
                  const timeHour  = parseInt(scheduleTime.split(":")[0]);
                  const congestionOk = termStat?.congestion!=="HIGH" || timeHour<7 || timeHour>11;
                  return (
                    <div style={{marginTop:10,display:"flex",flexDirection:"column",gap:5}}>
                      {[
                        {ok:daysOut===0,  warn:false, msg:`Scheduling for ${daysOut===0?"today":daysOut===1?"tomorrow":scheduleDate+" ("+daysOut+" days out)"}`},
                        {ok:storeOk,      warn:!storeOk, msg:storeOk?`Store inventory OK through ${scheduleDate}`:` Store hits critical in ${depletion?.minCritical?.toFixed(1)} days — this schedule is too late!`},
                        {ok:winOpen,      warn:!winOpen, msg:winOpen?`Pipeline window open on ${scheduleDate}`:` Pipeline window opens in ${pipeWin?.daysToWindow} days — may need to wait`},
                        {ok:congestionOk, warn:!congestionOk, msg:congestionOk?`Rack timing OK`:` ${termStat?.congestion} congestion at ${scheduleTime} — consider 06:00–07:00 or 13:00+ slot`},
                      ].map((c,ci)=>(
                        <div key={ci} style={{display:"flex",alignItems:"center",gap:7,fontSize:10.5,color:c.warn?"#EF4444":c.ok?"#16A34A":darkMode?"#7B8FAF":"#4A5E7A",fontFamily:"Arial,sans-serif"}}>
                          <span style={{fontSize:12}}>{c.warn?"":c.ok?"":"·"}</span>{c.msg}
                        </div>
                      ))}
                    </div>
                  );
                })()}
              </div>

              {/*  AI RECOMMENDATION  */}
              <div style={{background:darkMode?"rgba(200,164,74,.07)":"#F8FAFB",borderRadius:10,padding:"14px 16px",border:`1.5px solid ${darkMode?"rgba(200,164,74,.25)":"#F0D9A0"}`}}>
                <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:aiDispatchResult||aiDispatchLoading?12:0}}>
                  <div style={{display:"flex",alignItems:"center",gap:9}}>
                    <div style={{width:32,height:32,borderRadius:8,background:"#0D1B2A",display:"flex",alignItems:"center",justifyContent:"center",fontSize:16}}></div>
                    <div>
                      <div style={{fontSize:12,fontWeight:700,color:"#F4D398",fontFamily:"Arial,sans-serif"}}>AI Dispatch Optimizer</div>
                      <div style={{fontSize:9.5,color:darkMode?"#7B8FAF":"#8B6914"}}>Analyzes HOS, fit, history, timing, congestion</div>
                    </div>
                  </div>
                  <button onClick={runAIDispatch} disabled={aiDispatchLoading}
                    style={{padding:"8px 16px",borderRadius:8,border:"none",background:aiDispatchLoading?"rgba(107,114,128,.3)":"linear-gradient(135deg, #F4D398, #D4B278)",color:aiDispatchLoading?"#6B7280":"#0D1B2A",fontSize:11,fontWeight:700,cursor:aiDispatchLoading?"not-allowed":"pointer",fontFamily:"Arial,sans-serif",whiteSpace:"nowrap",flexShrink:0}}>
                    {aiDispatchLoading?" Analyzing...":" Optimize with AI"}
                  </button>
                </div>

                {aiDispatchLoading&&(
                  <div style={{textAlign:"center",padding:"14px 0",color:darkMode?"#7B8FAF":"#8B6914",fontSize:11,fontFamily:"Arial,sans-serif"}}>
                    Analyzing {CARRIER_FLEET.filter(c=>c.available>0).reduce((a,c)=>a+c.tractors.filter(t=>t.status==="AVAILABLE").length,0)} available drivers, HOS projections, route fit, and terminal conditions...
                  </div>
                )}

                {aiDispatchResult&&!aiDispatchResult.error&&(
                  <div style={{display:"flex",flexDirection:"column",gap:10}}>
                    {/* Recommendation card */}
                    <div style={{background:darkMode?"rgba(200,164,74,.1)":"rgba(200,164,74,.08)",borderRadius:8,padding:"12px 14px",border:`1px solid rgba(200,164,74,.3)`}}>
                      <div style={{display:"flex",justifyContent:"space-between",alignItems:"flex-start",gap:10,marginBottom:8}}>
                        <div>
                          <div style={{fontSize:11,fontWeight:700,color:"#F4D398",fontFamily:"Arial,sans-serif",marginBottom:3}}>Recommended Assignment</div>
                          <div style={{fontSize:12,fontWeight:800,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:"Arial,sans-serif"}}>
                            {CARRIER_FLEET.find(c=>c.id===aiDispatchResult.carrierId)?.name||aiDispatchResult.carrierId}
                          </div>
                          <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",marginTop:2}}>
                            {CARRIER_FLEET.flatMap(c=>c.tractors).find(t=>t.id===aiDispatchResult.truckId)?.unit} — {CARRIER_FLEET.flatMap(c=>c.tractors).find(t=>t.id===aiDispatchResult.truckId)?.driver}
                          </div>
                        </div>
                        <div style={{display:"flex",gap:10,flexShrink:0}}>
                          {aiDispatchResult.fitScore&&<div style={{textAlign:"center"}}><div style={{fontSize:18,fontWeight:900,color:"#F4D398",fontFamily:"Arial,sans-serif"}}>{aiDispatchResult.fitScore}%</div><div style={{fontSize:9,color:darkMode?"#7B8FAF":"#8B6914"}}>Fit score</div></div>}
                          {aiDispatchResult.estimatedCost&&<div style={{textAlign:"center"}}><div style={{fontSize:18,fontWeight:900,color:darkMode?"#E8EDF6":"#0D1B2A",fontFamily:"Arial,sans-serif"}}>${aiDispatchResult.estimatedCost?.toLocaleString()}</div><div style={{fontSize:9,color:darkMode?"#7B8FAF":"#4A5E7A"}}>Est. cost</div></div>}
                        </div>
                      </div>
                      <div style={{fontSize:10.5,color:darkMode?"#F4D398":"#8B6914",lineHeight:1.5,fontFamily:"Arial,sans-serif"}}>{aiDispatchResult.reasoning}</div>
                      {aiDispatchResult.recommendedTime&&(
                        <div style={{marginTop:6,fontSize:10.5,fontWeight:700,color:"#F4D398"}}>Recommended departure: {aiDispatchResult.recommendedTime}</div>
                      )}
                    </div>
                    {/* Warnings */}
                    {aiDispatchResult.warnings?.length>0&&aiDispatchResult.warnings.map((w,wi)=>(
                      <div key={wi} style={{fontSize:10.5,color:darkMode?"#FBBF24":"#D97706",display:"flex",gap:6,alignItems:"flex-start",fontFamily:"Arial,sans-serif"}}>
                        <span></span><span>{w}</span>
                      </div>
                    ))}
                    <div style={{fontSize:9.5,color:darkMode?"#7B8FAF":"#4A5E7A",fontFamily:"Arial,sans-serif"}}> Carrier and truck auto-selected below. Review and confirm.</div>
                  </div>
                )}

                {aiDispatchResult?.error&&(
                  <div style={{fontSize:10.5,color:darkMode?"#7B8FAF":"#4A5E7A",fontFamily:"Arial,sans-serif",lineHeight:1.5,marginTop:4}}>
                     {aiDispatchResult.error}
                  </div>
                )}
              </div>

              {/*  CARRIER SELECT  */}
              <div>
                <div style={{fontSize:10.5,fontWeight:700,color:darkMode?"#7B8FAF":"#4A5E7A",textTransform:"uppercase",letterSpacing:.6,marginBottom:10,fontFamily:"Arial,sans-serif"}}>Select Carrier</div>
                {(()=>{
                  const eligible = CARRIER_FLEET.filter(c=>c.available>0&&c.terminalAccess.includes(dispatchTarget.terminal||""));
                  if(!eligible.length) return <div style={{padding:"12px",borderRadius:8,background:darkMode?"rgba(239,68,68,.1)":"#FFF5F5",border:"1px solid rgba(239,68,68,.3)",fontSize:11,color:"#EF4444",textAlign:"center",fontFamily:"Arial,sans-serif"}}>No carriers with access to {TERMINALS.find(t=>t.id===dispatchTarget.terminal)?.short}. Consider alternate terminal or truck rack.</div>;
                  return (
                    <div style={{display:"flex",flexDirection:"column",gap:7}}>
                      {eligible.sort((a,b)=>(a.id===aiDispatchResult?.carrierId?-1:1)).map(c=>{
                        const isAI = c.id===aiDispatchResult?.carrierId;
                        const isSelected = dispatchCarrierId===c.id;
                        const availTrucks = c.tractors.filter(t=>t.status==="AVAILABLE"&&projectHOS(t.hos,scheduleDate,scheduleTime)>=4);
                        return (
                          <button key={c.id} onClick={()=>{setDispatchCarrierId(c.id);setDispatchTruckId(isAI&&aiDispatchResult?.truckId?aiDispatchResult.truckId:null);}}
                            style={{padding:"11px 14px",borderRadius:9,border:`2px solid ${isSelected?(isAI?"#F4D398":"#3B82F6"):darkMode?"#1E2840":"#DDE3EC"}`,background:isSelected?(isAI?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):(darkMode?"rgba(59,130,246,.1)":"#EFF6FF")):"transparent",cursor:"pointer",textAlign:"left",fontFamily:"Arial,sans-serif",transition:"all .12s"}}>
                            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center"}}>
                              <div style={{flex:1,minWidth:0}}>
                                <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:3}}>
                                  <span style={{fontSize:12,fontWeight:700,color:darkMode?"#E8EDF6":"#0D1B2A"}}>{c.name}</span>
                                  {isAI&&<span style={{fontSize:9,fontWeight:700,padding:"2px 6px",borderRadius:6,background:"#F4D398",color:"#0D1B2A"}}> AI Pick</span>}
                                </div>
                                <div style={{display:"flex",gap:12,fontSize:10,color:darkMode?"#7B8FAF":"#4A5E7A"}}>
                                  <span> {c.rating}</span>
                                  <span>Detention: {c.ytdDetentionHrs}h YTD</span>
                                  <span>O/S: {c.ytdOverShort>0?"+":""}{c.ytdOverShort} gal</span>
                                  <span>${c.rateBase.toFixed(4)}/gal</span>
                                </div>
                                <div style={{display:"flex",gap:8,marginTop:4,fontSize:9.5}}>
                                  <span style={{color:c.hazmatCert?"#16A34A":"#EF4444"}}>HazMat {c.hazmatCert?"":""}</span>
                                  <span style={{color:c.vaporRecovery?"#16A34A":"#F59E0B"}}>VR {c.vaporRecovery?"":""}</span>
                                  <span style={{color:darkMode?"#7B8FAF":"#4A5E7A"}}>{availTrucks.length} driver{availTrucks.length!==1?"s":""} w/ HOS at {scheduleTime}</span>
                                </div>
                              </div>
                              <div style={{width:20,height:20,borderRadius:"50%",background:isSelected?(isAI?"#F4D398":"#3B82F6"):"transparent",border:`2px solid ${isSelected?(isAI?"#F4D398":"#3B82F6"):darkMode?"#1E2840":"#DDE3EC"}`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,color:isSelected?"#fff":"transparent",flexShrink:0,marginLeft:10}}></div>
                            </div>
                          </button>
                        );
                      })}
                    </div>
                  );
                })()}
              </div>

              {/*  TRUCK SELECT  */}
              {dispatchCarrierId&&(()=>{
                const carrier = CARRIER_FLEET.find(c=>c.id===dispatchCarrierId);
                const avail = carrier?.tractors.filter(t=>t.status==="AVAILABLE")||[];
                return (
                  <div>
                    <div style={{fontSize:10.5,fontWeight:700,color:darkMode?"#7B8FAF":"#4A5E7A",textTransform:"uppercase",letterSpacing:.6,marginBottom:10,fontFamily:"Arial,sans-serif"}}>Select Driver / Truck</div>
                    {avail.length===0&&<div style={{fontSize:11,color:darkMode?"#7B8FAF":"#4A5E7A",padding:"10px",textAlign:"center"}}>No available trucks</div>}
                    <div style={{display:"flex",flexDirection:"column",gap:6}}>
                      {avail.sort((a,b)=>(a.id===aiDispatchResult?.truckId?-1:1)).map(t=>{
                        const projHOS = projectHOS(t.hos, scheduleDate, scheduleTime);
                        const hosOk = projHOS>=4;
                        const isAI = t.id===aiDispatchResult?.truckId;
                        const isSelected = dispatchTruckId===t.id;
                        const bestComp = carrier.compartments.reduce((best,c)=>Math.abs(c-(dispatchTarget.vol||0))<Math.abs(best-(dispatchTarget.vol||0))?c:best,carrier.compartments[0]);
                        const deadhead = Math.max(0,bestComp-(dispatchTarget.vol||0));
                        const fitPct = Math.round((1-deadhead/bestComp)*100);
                        return (
                          <button key={t.id} onClick={()=>hosOk&&setDispatchTruckId(t.id)} disabled={!hosOk}
                            style={{padding:"11px 14px",borderRadius:9,border:`2px solid ${isSelected?(isAI?"#F4D398":"#3B82F6"):darkMode?"#1E2840":"#DDE3EC"}`,background:isSelected?(isAI?(darkMode?"rgba(200,164,74,.12)":"#FFF9E6"):(darkMode?"rgba(59,130,246,.1)":"#EFF6FF")):!hosOk?(darkMode?"rgba(239,68,68,.06)":"#FFF5F5"):"transparent",cursor:hosOk?"pointer":"not-allowed",textAlign:"left",opacity:hosOk?1:0.6,fontFamily:"Arial,sans-serif",transition:"all .12s"}}>
                            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",gap:10}}>
                              <div style={{flex:1,minWidth:0}}>
                                <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:4}}>
                                  <div style={{width:28,height:28,borderRadius:"50%",background:"#F4D398",display:"flex",alignItems:"center",justifyContent:"center",fontSize:10,fontWeight:800,color:"#0D1B2A",flexShrink:0}}>
                                    {t.driver.split(" ").map(n=>n[0]).join("")}
                                  </div>
                                  <div>
                                    <div style={{display:"flex",alignItems:"center",gap:6}}>
                                      <span style={{fontSize:11,fontWeight:700,color:darkMode?"#E8EDF6":"#0D1B2A"}}>{t.unit} — {t.driver}</span>
                                      {isAI&&<span style={{fontSize:9,fontWeight:700,padding:"2px 6px",borderRadius:6,background:"#F4D398",color:"#0D1B2A"}}> AI</span>}
                                    </div>
                                    <div style={{fontSize:9.5,color:darkMode?"#7B8FAF":"#4A5E7A",marginTop:1}}>{t.location}</div>
                                  </div>
                                </div>
                                {/* HOS projection bar */}
                                <div style={{display:"flex",alignItems:"center",gap:8}}>
                                  <div style={{flex:1,height:5,background:darkMode?"rgba(255,255,255,.1)":"rgba(0,0,0,.08)",borderRadius:3,overflow:"hidden"}}>
                                    <div style={{height:"100%",width:`${(projHOS/11)*100}%`,background:projHOS>=8?"#22C55E":projHOS>=4?"#F59E0B":"#EF4444",borderRadius:3}}/>
                                  </div>
                                  <span style={{fontSize:10.5,fontWeight:700,color:projHOS>=8?"#22C55E":projHOS>=4?"#F59E0B":"#EF4444",whiteSpace:"nowrap"}}>{projHOS}h{scheduleDate!=="2025-04-18"?" (projected)":""}</span>
                                </div>
                                <div style={{display:"flex",gap:10,marginTop:4,fontSize:9.5,color:darkMode?"#7B8FAF":"#4A5E7A"}}>
                                  <span>Now: {t.hos}h HOS</span>
                                  <span>Fit: {fitPct}%</span>
                                  {deadhead>0&&<span style={{color:"#F59E0B"}}>+{deadhead.toLocaleString()} gal deadhead</span>}
                                  {!hosOk&&<span style={{color:"#EF4444",fontWeight:700}}>Insufficient HOS</span>}
                                </div>
                              </div>
                              <div style={{width:20,height:20,borderRadius:"50%",background:isSelected?(isAI?"#F4D398":"#3B82F6"):"transparent",border:`2px solid ${isSelected?(isAI?"#F4D398":"#3B82F6"):darkMode?"#1E2840":"#DDE3EC"}`,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,color:isSelected?"#fff":"transparent",flexShrink:0}}></div>
                            </div>
                          </button>
                        );
                      })}
                    </div>
                  </div>
                );
              })()}

              {/*  CONFIRM  */}
              {(()=>{
                const carrier = CARRIER_FLEET.find(c=>c.id===dispatchCarrierId);
                const tractor = carrier?.tractors.find(t=>t.id===dispatchTruckId);
                const ready = !!(dispatchCarrierId&&dispatchTruckId);
                const isToday = scheduleDate==="2025-04-18";
                const projHOS = tractor?projectHOS(tractor.hos,scheduleDate,scheduleTime):0;
                return (
                  <div style={{borderTop:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,paddingTop:14,display:"flex",flexDirection:"column",gap:8}}>
                    {ready&&(
                      <div style={{padding:"10px 14px",borderRadius:8,background:darkMode?"rgba(34,197,94,.08)":"#F0FDF4",border:"1px solid rgba(34,197,94,.3)",display:"flex",flexDirection:"column",gap:4,fontSize:10.5,fontFamily:"Arial,sans-serif"}}>
                        <div style={{fontWeight:700,color:"#16A34A",marginBottom:2}}> Ready to {isToday?"dispatch":"schedule"}</div>
                        <div style={{color:darkMode?"#7B8FAF":"#4A5E7A"}}>{carrier?.name} · {tractor?.unit} · {tractor?.driver}</div>
                        <div style={{color:darkMode?"#7B8FAF":"#4A5E7A"}}>{isToday?"Today":"On "+scheduleDate} at {scheduleTime} · HOS at departure: {projHOS}h</div>
                        {aiDispatchResult&&!aiDispatchResult.error&&<div style={{color:"#F4D398",fontWeight:600}}> AI-optimized selection</div>}
                      </div>
                    )}
                    <button onClick={doDispatch} disabled={!ready}
                      style={{width:"100%",padding:"13px 0",borderRadius:10,border:"none",background:ready?"#0D1B2A":"rgba(107,114,128,.25)",color:ready?"#0D1B2A":"#6B7280",fontSize:14,fontWeight:800,cursor:ready?"pointer":"not-allowed",fontFamily:"Arial,sans-serif",transition:"all .15s"}}>
                      {ready?(isToday?" Dispatch Now":" Schedule for "+scheduleDate+" "+scheduleTime):"Select carrier + driver to continue"}
                    </button>
                  </div>
                );
              })()}
            </div>
          </div>
        </div>
      )}

      {/*  AI Procurement Advisor — temporarily hidden. Restore by changing `false` to `true` below.  */}
      {false && <button onClick={()=>setShowAdvisor(true)}
        style={{position:"fixed",bottom:24,right:24,zIndex:500,width:52,height:52,borderRadius:"50%",background:"#0D1B2A",border:"none",boxShadow:"0 4px 20px rgba(200,164,74,.45)",cursor:"pointer",fontSize:22,display:"flex",alignItems:"center",justifyContent:"center"}}
        title="AI Procurement Advisor">
        
      </button>}

      {false && showAdvisor&&(
        <div style={{position:"fixed",bottom:90,right:24,zIndex:600,width:380,maxHeight:"70vh",background:darkMode?"#0D1522":"#FFFFFF",border:`1.5px solid ${darkMode?"rgba(200,164,74,.3)":"#DDE3EC"}`,borderRadius:14,boxShadow:"0 20px 60px rgba(0,0,0,.35)",display:"flex",flexDirection:"column",overflow:"hidden"}}>
          <div style={{padding:"14px 16px",background:darkMode?"#0F1B2A":"#0D1B2A",display:"flex",alignItems:"center",justifyContent:"space-between",flexShrink:0}}>
            <div style={{display:"flex",alignItems:"center",gap:10}}>
              <div style={{width:32,height:32,borderRadius:8,background:"#0D1B2A",display:"flex",alignItems:"center",justifyContent:"center",fontSize:16}}></div>
              <div>
                <div style={{fontSize:13,fontWeight:700,color:"#E8EDF6"}}>AI Procurement Advisor</div>
                <div style={{fontSize:9.5,color:"#F4D398"}}>Powered by Claude</div>
              </div>
            </div>
            <button onClick={()=>setShowAdvisor(false)} style={{background:"none",border:"none",color:"#7B8FAF",fontSize:18,cursor:"pointer",lineHeight:1}}></button>
          </div>
          <div style={{flex:1,overflowY:"auto",padding:16}}>
            {!advisorText&&!advisorLoading&&(
              <div>
                <div style={{fontSize:11,color:darkMode?"#7B8FAF":"#4A5E7A",lineHeight:1.6,marginBottom:12}}>
                  I analyze your live rack prices, inventory levels, pipeline status, and procurement signals to generate a daily buying recommendation.
                </div>
                <button onClick={async()=>{
                  setAdvisorLoading(true);
                  try {
                    const ANTHROPIC_API_KEY = "";
                    const headers = {"Content-Type":"application/json","anthropic-dangerous-direct-browser-access":"true"};
                    if(ANTHROPIC_API_KEY) { headers["x-api-key"]=ANTHROPIC_API_KEY; headers["anthropic-version"]="2023-06-01"; }
                    const topActions = ACTION_QUEUE.slice(0,5).map(a=>`• ${a.title}: ${a.desc}`).join("\n");
                    const critStores = DEPLETION.filter(d=>d.minCritical<=2).map(d=>d.storeName).join(", ")||"none";
                    const buySignals = TERMINALS.filter(t=>SIGNALS[t.id]?.Regular?.signal==="BUY NOW").map(t=>t.short).join(", ")||"none";
                    const waitSignals = TERMINALS.filter(t=>SIGNALS[t.id]?.Regular?.signal==="WAIT").map(t=>t.short).join(", ")||"none";
                    const res = await fetch("https://api.anthropic.com/v1/messages",{method:"POST",headers,
                      body:JSON.stringify({model:"claude-sonnet-4-6",max_tokens:600,
                        messages:[{role:"user",content:`You are a fuel procurement advisor for a 60-store c-store chain in NC, SC, VA, GA, FL. Be direct and specific.

TODAY: Apr 26, 2025 | Colonial ${COLONIAL.status} (L1: ${COLONIAL.line1Capacity}%, L2: ${COLONIAL.line2Capacity}%) | Nom deadline: ${COLONIAL.nominationDeadline}

ACTION QUEUE:
${topActions}

SIGNALS: BUY NOW at ${buySignals} | WAIT at ${waitSignals}
CRITICAL INVENTORY: ${critStores}
UNHEDGED EXPOSURE: ${(UNHEDGED/1000).toFixed(0)}K gal/month · $${(UNHEDGED*0.10/1000).toFixed(0)}K at risk per $0.10 move

Give me:
1. Top 3 specific buy orders to place today (terminal, grade, volume, why)
2. What to wait on and why
3. One risk I should be thinking about
4. One sentence on hedge posture

Be specific with dollar amounts and volumes. No fluff.`}]})});
                    const data = await res.json();
                    setAdvisorText(data.content?.[0]?.text||"No response");
                  } catch(e) { setAdvisorText("API key required. Add your Anthropic key to enable the AI advisor."); }
                  setAdvisorLoading(false);
                }} style={{width:"100%",padding:"10px",borderRadius:8,background:"#0D1B2A",border:"none",color:"#0D1B2A",fontWeight:700,fontSize:13,cursor:"pointer"}}>
                   Generate Morning Briefing
                </button>
              </div>
            )}
            {advisorLoading&&(
              <div style={{textAlign:"center",padding:"24px 0"}}>
                <div style={{fontSize:28,marginBottom:8}}></div>
                <div style={{fontSize:12,color:darkMode?"#7B8FAF":"#4A5E7A"}}>Analyzing market data…</div>
              </div>
            )}
            {advisorText&&!advisorLoading&&(
              <div>
                <div style={{fontSize:11,color:darkMode?"#E8EDF6":"#0D1B2A",lineHeight:1.7,whiteSpace:"pre-wrap"}}>{advisorText}</div>
                <button onClick={()=>setAdvisorText("")} style={{marginTop:12,width:"100%",padding:"8px",borderRadius:7,border:`1px solid ${darkMode?"#1E2840":"#DDE3EC"}`,background:"transparent",color:darkMode?"#7B8FAF":"#4A5E7A",fontSize:11,cursor:"pointer"}}>
                  Generate New Briefing
                </button>
              </div>
            )}
          </div>
        </div>
      )}

    </div>
  );
}
