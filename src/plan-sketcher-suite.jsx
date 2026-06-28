import React, { useState, useRef, useMemo, useEffect, useCallback } from "react";
// Shear-wall calculation engine (verbatim Struware port) lives in its own module
// as of the rev-33 split — see calcCore.js. Behavior is byte-identical; this file
// imports the engine rather than defining it inline.
import {
  calcSegment, generateDesign, baseDesignSeg, schedFor,
  HD_TABLE, NAIL_EDGE, CODES, isNum, xMax, numOr0,
} from "./calcCore.js";

// ── APP DISPLAY VERSION (user-facing build number shown in the top bar) ──────
// Bump APP_BUILD by 1 on every app update. Rendered as major.minor with a 2-digit minor that
// rolls over at 99 → next major: 100→"1.00", 101→"1.01", … 199→"1.99", 200→"2.00". Integer math
// (no float formatting), so the rollover is correct by construction.
// NOTE — this is ONE OF THREE independent counters; keep them distinct:
//   • APP_VERSION (here)      — human-facing build number in the UI ("Version 1.00").
//   • CURRENT_VERSION (~below)— save-file SCHEMA version; drives .wps migrations. Do NOT couple.
//   • handoff "rev" number    — the dev changelog in PLAN_SKETCHER_SUITE_HANDOFF.md.
const APP_BUILD = 153;                                                                 // +1 per release
const APP_VERSION = `${Math.floor(APP_BUILD / 100)}.${String(APP_BUILD % 100).padStart(2, "0")}`;  // "1.00"

// ── geometry space: 1 unit = 1 ft ──────────────────────────────────────────
const VB_W = 100, VB_H = 75, GRID = 5, PAD = 2;
const WORLD = 4000;            // plan coords may span -WORLD..+WORLD (origin is arbitrary)
// pick a "nice" grid step so a plan of any size shows a sensible number of lines
const niceStep = (span) => {
  const steps=[0.5,1,2,5,10,25,50,100,250,500,1000];   // rev 64: 0.5 ft is now the finest grid/snap increment (was 1 ft)
  const target=span/22;        // aim for ~22 divisions across the view
  for(const s of steps) if(s>=target) return s;
  return 1000;
};

const PRESETS = {
  Rectangle: [{ x:20,y:18 },{ x:80,y:18 },{ x:80,y:57 },{ x:20,y:57 }],
  "L-shape":  [{ x:20,y:15 },{ x:60,y:15 },{ x:60,y:38 },{ x:80,y:38 },{ x:80,y:60 },{ x:20,y:60 }],
  "U-shape":  [{ x:20,y:15 },{ x:40,y:15 },{ x:40,y:45 },{ x:60,y:45 },{ x:60,y:15 },{ x:80,y:15 },{ x:80,y:60 },{ x:20,y:60 }],
  Triangle:   [{ x:50,y:15 },{ x:80,y:60 },{ x:20,y:60 }],
};

// ── helpers ────────────────────────────────────────────────────────────────
const clamp   = (v,lo,hi) => Math.min(hi, Math.max(lo, v));
const dist    = (a,b)     => Math.hypot(b.x-a.x, b.y-a.y);
const edgeAxis= (a,b)     => Math.abs(b.x-a.x) >= Math.abs(b.y-a.y) ? "h" : "v";
const norm    = (a,b)     => a < b ? {a,b} : {a:b,b:a};
const same    = (e1,e2)   => e1 && e2 && e1.a===e2.a && e1.b===e2.b;
const keyOf   = (e)       => `${e.a}-${e.b}`;
const fmt1    = (n)       => Math.round(n*10)/10;
const fmt2    = (n)       => Math.round(n*100)/100;
const fmtHalf = (n)       => Math.round(n*2)/2;   // rev 64: snap a dimension label to the nearest 0.5 ft (e.g. 10.5)
// text rotation that keeps labels parallel to a wall and upright (-90..90]
const wallAng = (dx,dy)=>{ let a=Math.atan2(dy,dx)*180/Math.PI; a=((a+90)%180+180)%180-90; return a; };
// (rev 57) SEISMIC EFFECTIVE WEIGHT — 1-STORY.  W_total = roof + walls (lbs).
//   W_roof  = enclosed plan area (ft²) × Roof DL (psf)
//   per wall: H_trib = par + H/2  — the full parapet (above the diaphragm) + half the story height
//             below it (the lower half spans to the foundation); W = H_trib × length × Wall DL (psf).
//   W_wall  = Σ over every wall.  Pure + 1-STORY ONLY (the 2-story per-diaphragm tributary split lands
//   in a later step). Reads each wall's own par/H via propsFor, so it tracks Global Inputs / section cuts.
//   `profiles` groups equal (par,H) walls for a per-profile readout — the sum is identical either way.
function seismicWeight1Story(graph, loop, propsFor, roofDL, wallDL){
  const area = (loop && loop.area) ? loop.area : 0;
  const Wroof = area * (roofDL||0);
  let Wwall = 0; const byProfile = new Map();
  for(const e of graph.edges){
    const a = graph.nodes.find(n=>n.id===e.a), b = graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    const len = Math.hypot(b.x-a.x, b.y-a.y);
    const p = propsFor(keyOf(e)); const par = p.par||0, H = p.H||0;
    const htrib = par + H/2; const w = htrib * len * (wallDL||0);
    Wwall += w;
    const k = `${par}|${H}`;
    const g = byProfile.get(k) || { par, H, htrib, len:0, w:0 };
    g.len += len; g.w += w; byProfile.set(k, g);
  }
  return { area, Wroof, Wwall, Wtotal: Wroof + Wwall, profiles:[...byProfile.values()] };
}
// (rev 60) SEISMIC EFFECTIVE WEIGHT — 2-STORY.  The tributary wall weight SPLITS between the floor
// diaphragm (level 1) and the roof diaphragm (level 2); each level is tracked independently so the
// base shear V = Cs·W_total can be distributed vertically (Phase 3).  Per SECTION-B (2 STORY):
//   Level 2 (roof):   area×roofDL  +  Σ over 2-STORY walls of (par + H₂/2)·len·wallDL
//                     (full parapet above + the UPPER half of story 2).      e.g. 6 + 10/2 = 11 ft
//   Level 1 (floor):  area×floorDL +  Σ over walls of H_trib·len·wallDL where
//                       2-story wall → H₂/2 + H₁/2  (lower half of story 2 + upper half of story 1)
//                                                                            e.g. 5 + 6.5 = 11.5 ft
//                       1-story wall → par + H₁/2   (its own parapet + upper half — its roof sits at
//                                                    the floor-diaphragm level; mixed-height C/D)
//   The remaining bottom half of story 1 (H₁/2) dumps to the foundation and is excluded.
// Area DL by level (handles mixed height): the 2-story footprint (twoStoryLoop) carries a real FLOOR
// at level 1 (floorDL) and a ROOF at level 2 (roofDL); any 1-story-only footprint carries its ROOF at
// level 1 (roofDL).  Uniform 2-story → roofArea==floorArea, so floor = floorDL·area, roof = roofDL·area.
// Diaphragm elevations above grade: h_floor = H₁, h_roof = H₁ + H₂ (representative story heights from
// the 2-story walls).  isOne(key) = wall tagged 1-story.  Pure; reads each wall's par/H/H₂ via propsFor.
function seismicWeight2Story(graph, loop, twoStoryLoop, propsFor, isOne, roofDL, floorDL, wallDL){
  const floorArea = (loop && loop.area) ? loop.area : 0;
  const roofArea  = (twoStoryLoop && twoStoryLoop.area) ? twoStoryLoop.area
                  : ((loop && loop.area) ? loop.area : 0);           // closed 2-story sub-loop, else full
  const oneStoryArea = Math.max(0, floorArea - roofArea);            // footprint that is 1-story only
  const WroofArea  = roofArea  * (roofDL||0);
  const WfloorArea = floorArea===0 ? 0 : (roofArea*(floorDL||0) + oneStoryArea*(roofDL||0));
  let WroofWall=0, WfloorWall=0, H1rep=0, H2rep=0; const byProfile = new Map();
  for(const e of graph.edges){
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    const len=Math.hypot(b.x-a.x, b.y-a.y);
    const k=keyOf(e); const p=propsFor(k);
    const par=p.par||0, H1=p.H||0, H2=(p.H2!=null?p.H2:p.H)||0;
    const one = isOne ? isOne(k) : false;
    let htR=0, htF=0;
    if(one){ htF = par + H1/2; }                                     // 1-story wall → floor diaphragm only
    else   { htR = par + H2/2; htF = H2/2 + H1/2;                    // 2-story wall → both diaphragms
             H1rep=Math.max(H1rep,H1); H2rep=Math.max(H2rep,H2); }
    WroofWall  += htR*len*(wallDL||0);
    WfloorWall += htF*len*(wallDL||0);
    const pk=`${one?"1":"2"}|${par}|${H1}|${H2}`;
    const g=byProfile.get(pk)||{one,par,H1,H2,htR,htF,len:0,wR:0,wF:0};
    g.len+=len; g.wR+=htR*len*(wallDL||0); g.wF+=htF*len*(wallDL||0); byProfile.set(pk,g);
  }
  if(H1rep===0){ for(const e of graph.edges){ const p=propsFor(keyOf(e)); H1rep=Math.max(H1rep,p.H||0); H2rep=Math.max(H2rep,(p.H2!=null?p.H2:p.H)||0); } }
  const Wroof=WroofArea+WroofWall, Wfloor=WfloorArea+WfloorWall;
  const hFloor=H1rep, hRoof=H1rep+H2rep;
  return { floorArea, roofArea, WroofArea, WfloorArea, WroofWall, WfloorWall,
           Wroof, Wfloor, Wtotal:Wroof+Wfloor, hFloor, hRoof, profiles:[...byProfile.values()] };
}
// (rev 60) Phase 3 — vertical distribution of base shear V across the two diaphragm levels by
// F_level = V·(W_level·h_level)/Σ(W·h).  Returns V + the roof/floor forces (lbs).
function seismicDistribute2Story(sw2, Cs){
  if(!sw2) return null;
  const V = (Cs||0) * sw2.Wtotal;
  const whR = sw2.Wroof*sw2.hRoof, whF = sw2.Wfloor*sw2.hFloor, sum = whR+whF;
  return { V, Froof: sum>0 ? V*whR/sum : 0, Ffloor: sum>0 ? V*whF/sum : 0, sumWh:sum };
}
// a section now stores its own shared values (per wind direction)
const DEF_SECTION = { H:10, pw:16, qWind:32, qLee:22, par:5, H2:null,
                      // (rev 49) DEAD-LOAD TRIBUTARY — now a per-wall, per-floor property entered on the
                      // plan (right-click wall → "DL Tributary"), replacing the old GLOBAL Design-tab
                      // Roof/Floor trib boxes. floorTrib/roofTrib = 1st-floor (and 1-story) values;
                      // floorTrib2/roofTrib2 = 2nd-floor values (used when designing/viewing floor 2 of a
                      // 2-story building, so a stacked wall can carry a different trib on each floor).
                      // Defaults match the old global default (roof 2 ft, floor 0 ft) → untouched walls
                      // behave exactly as before. mergeWallProps fills these from DEF_SECTION, so old .wps
                      // files inherit them automatically (not part of the loadProject schema tripwire).
                      roofTrib:2, floorTrib:0, roofTrib2:2, floorTrib2:0 };  // (rev 44) default wall H=10ft, parapet=5ft. `par` = this wall's own parapet; `H2` = 2nd-story wall ht (2-story mode), null → equals H
// Normalize one stored wall-prop entry: migrate the legacy `parW` field, then MERGE ONTO
// DEF_SECTION so a saved entry that predates a future field still resolves every key (no NaN
// from an `undefined` pressure term). Behavior-identical for current entries (they override
// every DEF_SECTION key); the merge only fills keys an OLD file happens to lack. `propsFor`
// is the sole caller; kept module-scope (pure) so the load-robustness test can exercise it.
const mergeWallProps = (p) => {
  if(!p) return { ...DEF_SECTION, H2:DEF_SECTION.H };          // no saved props → H2 defaults to H
  const base = ("par" in p) ? p : { ...p, par:(p.parW!=null?p.parW:DEF_SECTION.par) };  // legacy parW → par
  const out  = { ...DEF_SECTION, ...base };
  if(out.H2==null) out.H2 = out.H;                            // unset 2nd-story ht → equals 1st-story H (old files + new walls)
  return out;
};

// segment p1p2 ∩ segment p3p4 → {pt,t} (t = param along p1→p2) or null
const segInt = (p1,p2,p3,p4) => {
  const d1x=p2.x-p1.x, d1y=p2.y-p1.y, d2x=p4.x-p3.x, d2y=p4.y-p3.y;
  const den=d1x*d2y - d1y*d2x;
  if (Math.abs(den)<1e-9) return null;
  const t=((p3.x-p1.x)*d2y-(p3.y-p1.y)*d2x)/den;
  const u=((p3.x-p1.x)*d1y-(p3.y-p1.y)*d1x)/den;
  if (t<-1e-6||t>1+1e-6||u<-1e-6||u>1+1e-6) return null;
  return { pt:{x:p1.x+t*d1x, y:p1.y+t*d1y}, t };
};

// (rev 64) Foot of the perpendicular from point p onto the segment a–b.
//   t  = parameter along a→b (UNclamped: 0..1 means the foot lies on the body; ≤0 / ≥1 means
//        it falls beyond an endpoint — the caller rejects those so we only split the body).
//   dist = perpendicular distance from p to the infinite line (the value the caller compares to
//        the snap tolerance; meaningful exactly when 0<t<1, which is the only case we accept).
const projToSeg = (p, a, b) => {
  const dx=b.x-a.x, dy=b.y-a.y, L2=dx*dx+dy*dy;
  if(L2<1e-12) return { pt:{x:a.x,y:a.y}, t:0, dist:Math.hypot(p.x-a.x,p.y-a.y) };
  const t=((p.x-a.x)*dx+(p.y-a.y)*dy)/L2;
  const fx=a.x+t*dx, fy=a.y+t*dy;
  return { pt:{x:fx,y:fy}, t, dist:Math.hypot(p.x-fx,p.y-fy) };
};

// (rev 71) Point a fixed distance `len` from `anchor` along direction `dir` ({dx,dy}). Used by the
// Tab/dynamic-length draw input (AutoCAD-style: type a length, the next node lands exactly that far
// along the current rubber-band heading). Degenerate dir → returns the anchor unchanged.
const pointAtLength = (anchor, dir, len) => {
  const L=Math.hypot(dir.dx,dir.dy);
  if(!(L>1e-9)) return { x:anchor.x, y:anchor.y };
  return { x:anchor.x+(dir.dx/L)*len, y:anchor.y+(dir.dy/L)*len };
};

// (rev 71) Clamp a world point into the visible viewBox (minus a margin) so a label anchored to it
// can never sit off-screen. Used to keep the rubber-band length label at the edge of the view when
// the segment's midpoint scrolls out of frame (AutoCAD keeps the dynamic dimension on-screen).
const clampPtToView = (pt, view, margin=0) => ({
  x: clamp(pt.x, view.x+margin, view.x+view.w-margin),
  y: clamp(pt.y, view.y+margin, view.y+view.h-margin),
});

// (rev 71) Two-finger pinch/zoom-pan transform. Given the viewBox at gesture start (view0), the SVG
// client rect, the WORLD point under the start midpoint (midWorld), the CURRENT screen midpoint of
// the two touches, and the start/current finger spreads (d0,d), returns the new viewBox. Spreading
// the fingers (d>d0) zooms IN (smaller viewBox); the midpoint translation gives two-finger pan in
// the same gesture. Aspect is preserved; the span is clamped to [vmin,vmax]. Pure → unit-testable.
const pinchTransform = (view0, rect, midWorld, curMid, d0, d, vmin, vmax) => {
  const f = (d0>0 && d>0) ? d0/d : 1;
  const aspect = view0.h/view0.w;
  const w = clamp(view0.w*f, vmin, vmax);
  const h = w*aspect;
  const fx = rect.width  ? (curMid.x-rect.left)/rect.width  : 0.5;
  const fy = rect.height ? (curMid.y-rect.top )/rect.height : 0.5;
  return { x: midWorld.x - fx*w, y: midWorld.y - fy*h, w, h };
};

// (rev 72) Spreadsheet-style column name for a 1-based index: 1→A, 26→Z, 27→AA … Used to letter the
// E–W (horizontal) grid lines in the Design tab. Pure → unit-testable.
const colName = (n) => { let s=""; let k=Math.max(1,Math.floor(n)); while(k>0){ const r=(k-1)%26; s=String.fromCharCode(65+r)+s; k=Math.floor((k-1)/26); } return s; };

// outermost two walls a cut line crosses → {front,back} each {edge,pt} (front = lower t)
const computeCut = (line, graph) => {
  const p1={x:line.x1,y:line.y1}, p2={x:line.x2,y:line.y2};
  const hits=[];
  for (const e of graph.edges) {
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    const r=segInt(p1,p2,a,b);
    if(r) hits.push({edge:e, t:r.t, pt:r.pt});
  }
  if(hits.length<2) return null;
  hits.sort((x,y)=>x.t-y.t);
  return { front:hits[0], back:hits[hits.length-1] };
};

const buildFrom = (pts, startId) => ({
  graph: {
    nodes: pts.map((p,i)=>({ id:startId+i, ...p })),
    edges: pts.map((_,i)=>norm(startId+i, startId+(i+1)%pts.length)),
  },
  nextId: startId + pts.length,
});

// (rev 67) GRAPH SANITIZER — the perimeter tracer below (and the seismic roof area + plf that
// depend on it) hard-fail if the graph carries an ORPHAN edge (one whose endpoint node was deleted
// without the edge being removed), a duplicate edge, or a self-loop. Such a stray edge is invisible
// on the canvas but pushes a node off degree-2 / makes edges≠nodes, so loopInfo returns null and the
// roof area silently reads blank with W_roof=0. This pure helper drops exactly those defects and
// nothing else: a well-formed closed plan passes through UNCHANGED (so a valid graph's area is
// byte-identical to before). Applied (a) on .wps load, so any already-saved corrupt file self-heals
// and a re-save is clean, and (b) inside loopInfo, so even a transient in-session stray edge can't
// blank the area. It does NOT alter node positions or add geometry.
const sanitizeGraph = (graph) => {
  if(!graph || !Array.isArray(graph.nodes) || !Array.isArray(graph.edges)) return graph;
  const ids = new Set(graph.nodes.map(n=>n.id));
  const seen = new Set();
  const edges = [];
  for(const e of graph.edges){
    if(!e || e.a===e.b) continue;                 // drop self-loops
    if(!ids.has(e.a) || !ids.has(e.b)) continue;  // drop orphan edges (endpoint node missing)
    const k = keyOf(norm(e.a,e.b));               // normalized key → dedupe undirected duplicates
    if(seen.has(k)) continue;
    seen.add(k); edges.push(e);
  }
  // preserve object identity when nothing changed (avoids needless re-renders / memo churn)
  return edges.length===graph.edges.length ? graph : { ...graph, edges };
};

const loopInfo = (nodes, edges) => {
  // (rev 67) heal an orphan/duplicate/self-loop edge before tracing, so a closed plan that carries
  // an invisible stray edge still yields its area. A clean ring is unaffected (sanitize is a no-op).
  ({ nodes, edges } = sanitizeGraph({ nodes, edges }));
  const n = nodes.length;
  if (n < 3 || edges.length !== n) return null;
  const adj = new Map(nodes.map(nd=>[nd.id,[]]));
  for (const e of edges) {
    if (!adj.has(e.a)||!adj.has(e.b)) return null;
    adj.get(e.a).push(e.b); adj.get(e.b).push(e.a);
  }
  for (const nd of nodes) if (adj.get(nd.id).length !== 2) return null;
  const order=[], byId = id => nodes.find(nd=>nd.id===id);
  let prev=null, cur=nodes[0].id;
  for (let k=0;k<n;k++) {
    order.push(cur);
    const nb=adj.get(cur), nxt=nb[0]!==prev?nb[0]:nb[1];
    prev=cur; cur=nxt;
  }
  if (cur!==nodes[0].id || new Set(order).size!==n) return null;
  const ring=order.map(byId);
  let a=0;
  for (let i=0;i<ring.length;i++) { const p=ring[i],q=ring[(i+1)%ring.length]; a+=p.x*q.y-q.x*p.y; }
  return { area:Math.abs(a)/2, ring };
};

const INIT = buildFrom(PRESETS.Rectangle, 0);

// ray-cast point-in-polygon (works for concave rings like U / L shapes)
const pointInRing = (px,py,ring) => {
  let inside=false;
  for(let i=0,j=ring.length-1;i<ring.length;j=i++){
    const xi=ring[i].x, yi=ring[i].y, xj=ring[j].x, yj=ring[j].y;
    if(((yi>py)!==(yj>py)) && (px < (xj-xi)*(py-yi)/(yj-yi)+xi)) inside=!inside;
  }
  return inside;
};

// The leeward (back) exterior wall a windward wall looks across to, for the leeward-parapet term:
// same orientation, downwind, overlapping the lookup position, and the FARTHEST downwind such wall
// (the exterior back face). The lookup position is `sAt` when given (the across-wind location of
// the section cut) else the windward wall's center — so when the back is one wall every front
// segment resolves to it (shared parapet), and when the back is split the specific segment behind
// THIS cut is returned. Returns an edge key or null.
const findLeewardPartner = (windKey, axis, sign, graph, sAt) => {
  if(sign==null) return null;
  const travel = axis==="v" ? {x:0,y:sign} : {x:sign,y:0};
  const wEdge = graph.edges.find(e=>keyOf(e)===windKey); if(!wEdge) return null;
  const wa=graph.nodes.find(n=>n.id===wEdge.a), wb=graph.nodes.find(n=>n.id===wEdge.b); if(!wa||!wb) return null;
  const sOf  = p=> axis==="v"?p.x:p.y;                 // across-wind position
  const along= p=> p.x*travel.x + p.y*travel.y;        // downwind depth (bigger = further downwind)
  const sC = (sAt!=null) ? sAt : (sOf(wa)+sOf(wb))/2;  // lookup at the cut, else the wall's center
  const dW = (along(wa)+along(wb))/2;
  const recv = axis==="v" ? "h" : "v";                 // across-wind walls (windward/leeward faces)
  let best=null, bestAlong=-Infinity;
  for(const e of graph.edges){
    if(keyOf(e)===windKey) continue;
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b); if(!a||!b) continue;
    if(edgeAxis(a,b)!==recv) continue;
    const s0=Math.min(sOf(a),sOf(b)), s1=Math.max(sOf(a),sOf(b));
    if(sC < s0-0.6 || sC > s1+0.6) continue;           // must sit behind the lookup position
    const d=(along(a)+along(b))/2;
    if(d <= dW+0.6) continue;                           // must be downwind
    if(d > bestAlong){ bestAlong=d; best=keyOf(e); }    // farthest downwind = exterior back
  }
  return best;
};

// Reaction engine — treats a windward wall LINE (all collinear windward segments at one depth)
// as a beam carried by the walls parallel to the wind. Each segment contributes a distributed
// load (plf) over its span; the line is split into simply-supported bays between consecutive
// supports; a load crossing an interior support is split at it; each bay distributes by statics
// (reference-side support takes W·(TL−X)/TL, far side W·X/TL); load outside the outermost
// supports cantilevers onto the nearest support. Reactions are independent of how the line is
// segmented when the segment plf values match — so adding a node never changes the point loads.
// `line` = { depth, segs:[{s0,s1,plf}], smin, smax }; s is the across-wind coord (ref = min s).
function lineReactions(line, graph, isSup, travel, sOf, along){
  const tol=0.8;
  const sup=[];
  for(const e of graph.edges){
    if(!isSup(keyOf(e))) continue;
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    const ex=b.x-a.x, ey=b.y-a.y, el=Math.hypot(ex,ey)||1;
    if(Math.abs((ex*travel.x+ey*travel.y)/el) < 0.5) continue;        // must run PARALLEL to wind
    const s=(sOf(a)+sOf(b))/2;
    if(s < line.smin-tol || s > line.smax+tol) continue;             // within the line's span
    const aMin=Math.min(along(a),along(b)), aMax=Math.max(along(a),along(b));
    // A parallel wall supports this windward LINE if it lies at or downwind of the windward face.
    // (It need NOT span all the way back to the windward depth: a re-entrant interior wall — e.g.
    // the step wall of an L — is tied to the windward face by the diaphragm and acts as an interior
    // support, just like a full-depth interior wall does. Only walls entirely UPWIND of the windward
    // face are rejected — those belong to a deeper windward line in a concave footprint.)
    if(aMax < line.depth - tol) continue;     // support is at or downwind of the windward face
    const upwind = along(a) <= along(b) ? a : b;                     // toward the windward side
    const downwind = upwind===a ? b : a;
    const ax=upwind.x+(downwind.x-upwind.x)/3, ay=upwind.y+(downwind.y-upwind.y)/3;
    sup.push({ s, key:keyOf(e), ax, ay, alen:el });
  }
  if(!sup.length) return { reactions:[], imbalance:true };
  // cluster collinear supports (a support split by a node is ONE support line); keep the longest
  sup.sort((u,v)=>u.s-v.s);
  const cl=[];
  for(const x of sup){
    const c=cl[cl.length-1];
    if(c && Math.abs(x.s-c.s)<0.75){ if(x.alen>c.alen){ c.s=x.s; c.key=x.key; c.ax=x.ax; c.ay=x.ay; c.alen=x.alen; } }
    else cl.push({...x});
  }
  const R={}; cl.forEach(c=>R[c.key]=0);
  const first=cl[0], last=cl[cl.length-1];
  for(const seg of line.segs){
    // left / right cantilever → nearest support
    if(seg.s0 < first.s-1e-9){ const c1=Math.min(seg.s1,first.s); if(c1>seg.s0) R[first.key]+=seg.plf*(c1-seg.s0); }
    if(seg.s1 > last.s +1e-9){ const c0=Math.max(seg.s0,last.s ); if(seg.s1>c0) R[last.key ]+=seg.plf*(seg.s1-c0); }
    // interior bays (simply supported, load split at each interior support)
    for(let i=0;i<cl.length-1;i++){
      const sa=cl[i].s, sb=cl[i+1].s, TL=sb-sa; if(TL<=1e-9) continue;
      const c0=Math.max(seg.s0,sa), c1=Math.min(seg.s1,sb); if(c1<=c0) continue;
      const W=seg.plf*(c1-c0), X=((c0+c1)/2)-sa;
      R[cl[i].key]   += W*(TL-X)/TL;
      R[cl[i+1].key] += W*X/TL;
    }
  }
  const reactions=cl.filter(c=>Math.abs(R[c.key])>1e-9)
                    .map(c=>({ key:c.key, kips:R[c.key]/1000, ax:c.ax, ay:c.ay }));
  return { reactions, imbalance:false };
}

// (rev 58, Step 2 / Option B) buildSecData's per-wall LINE LOAD is supplied by a load MODEL, so the
// same windward-collection + across-wind shadow + reaction geometry can carry a SEISMIC load
// (uniform V / projected-extent) as well as wind. The DEFAULT model reproduces the exact wind
// arithmetic verbatim — `base` = ½·H·pw + par·qWind (uniform over a wall) and `lee` = leePar·qLee
// (the leeward-parapet term, taken per back-wall sub-span) — so the wind path is byte-identical
// (proven by a golden-output regression). A seismic caller (Step 3) passes { base:()=>V/extent, lee:()=>0 }.
const WIND_LOAD = {
  base: (pr)=> 0.5*(pr.H||0)*(pr.pw||0) + (pr.par||0)*(pr.qWind||0),
  lee:  (pr, leePar)=> leePar*(pr.qLee||0),
};
// wind field for one direction: loads EVERY windward-facing wall of that orientation
function buildSecData(section, graph, loop, isSup, propsFor, loadModel){
  if(!section) return null;
  const { axis, sign } = section;
  const LM = loadModel || WIND_LOAD;   // (rev 58) default = wind; seismic supplies a uniform model
  const travel = axis==="v" ? {x:0,y:sign} : {x:sign,y:0};
  const ring = loop?loop.ring:null;
  let cx=0,cy=0,cn=0;
  (ring||graph.nodes).forEach(p=>{cx+=p.x;cy+=p.y;cn++;}); if(cn){cx/=cn;cy/=cn;}
  const extN=(a,b)=>{                                     // exterior normal (robust for concave)
    const dx=b.x-a.x, dy=b.y-a.y, len=Math.hypot(dx,dy)||1;
    let nx=-dy/len, ny=dx/len;
    const mx=(a.x+b.x)/2, my=(a.y+b.y)/2;
    if(ring){ if(pointInRing(mx+nx*0.4,my+ny*0.4,ring)){ nx=-nx; ny=-ny; } }
    else { if((mx-cx)*nx+(my-cy)*ny<0){ nx=-nx; ny=-ny; } }
    return {nx,ny,len};
  };
  const windLoads=[];
  for(const e of graph.edges){
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    // receiving walls run across the wind: axis 'v' (N–S wind) → horizontal walls, etc.
    const wallAxis=edgeAxis(a,b);
    if(axis==="v" ? wallAxis!=="h" : wallAxis!=="v") continue;
    const {nx,ny,len}=extN(a,b);
    if(nx*travel.x + ny*travel.y >= -1e-6) continue;    // keep only windward (faces the wind)
    windLoads.push({ wa:a, wb:b, nx, ny, len, key:keyOf(e) });
  }
  {
    // across-wind overlap test: drop a windward wall only when another windward wall
    // sits directly in front of it (same wind direction) — avoids double-counting.
    const along=(p)=> p.x*travel.x + p.y*travel.y;        // bigger = further downwind
    const tran =(p)=> -p.y*travel.x + p.x*travel.y;       // across-wind position
    const ov=(a0,a1,b0,b1)=> Math.min(Math.max(a0,a1),Math.max(b0,b1)) - Math.max(Math.min(a0,a1),Math.min(b0,b1));
    const kept = windLoads.filter(w=>{
      const wa0=tran(w.wa), wa1=tran(w.wb), aw=along({x:(w.wa.x+w.wb.x)/2,y:(w.wa.y+w.wb.y)/2});
      const overlapShadow = windLoads.some(u=>{
        if(u===w) return false;
        const au=along({x:(u.wa.x+u.wb.x)/2,y:(u.wa.y+u.wb.y)/2});
        return au < aw-0.5 && ov(wa0,wa1,tran(u.wa),tran(u.wb)) > 0.5;
      });
      return !overlapShadow;
    });
    let anyImbalance=false;
    const sOf =(p)=> axis==="v" ? p.x : p.y;     // across-wind coord (reference = min: left / top)
    kept.forEach(w=>{
      const pr=propsFor(w.key);
      // representative plf for the on-plan label: leeward parapet from the back wall behind centre
      const cLee=findLeewardPartner(w.key, axis, sign, graph);
      const cPar=cLee ? (propsFor(cLee).par||0) : 0;
      w.total = LM.base(pr) + LM.lee(pr, cPar);
      w.tdir=travel;
    });
    const drawn = kept.filter(w=>w.total>0);

    // Group drawn windward segments into collinear LINES (same along-wind depth). Each windward
    // wall is subdivided where the back (leeward) wall behind it changes, so the leeward-parapet
    // term is taken per region from the actual back wall — e.g. a single front wall over a split
    // back loads with each back segment's own parapet. A wall split into front segments is still
    // one line, so splitting alone never changes the point loads.
    const recv = axis==="v" ? "h" : "v";
    let alMin=Infinity, alMax=-Infinity;
    graph.nodes.forEach(p=>{ const al=along(p); if(al<alMin)alMin=al; if(al>alMax)alMax=al; });
    const lines=[];
    drawn.forEach(w=>{
      const depth=(along(w.wa)+along(w.wb))/2;
      let L=lines.find(l=>Math.abs(l.depth-depth)<0.6);
      if(!L){ L={depth, segs:[], smin:Infinity, smax:-Infinity}; lines.push(L); }
      const ws0=Math.min(sOf(w.wa),sOf(w.wb)), ws1=Math.max(sOf(w.wa),sOf(w.wb));
      const pr=propsFor(w.key);
      const base = LM.base(pr);   // uniform over the wall (wind: ½·H·pw + par·qWind; seismic: V/extent)
      // back walls overlapping this windward wall (downwind), as {lo,hi,d,par}
      const backs=[];
      for(const e of graph.edges){
        if(keyOf(e)===w.key) continue;
        const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b); if(!a||!b) continue;
        if(edgeAxis(a,b)!==recv) continue;
        const d=(along(a)+along(b))/2; if(d<=depth+0.6) continue;          // downwind only
        const lo=Math.max(ws0,Math.min(sOf(a),sOf(b))), hi=Math.min(ws1,Math.max(sOf(a),sOf(b)));
        if(hi-lo>0.5) backs.push({ lo, hi, d, par:(propsFor(keyOf(e)).par||0) });
      }
      // subdivide the windward span at back-wall breakpoints; each sub-span uses the farthest
      // downwind back covering it (the exterior back face) for its leeward parapet
      const bps=new Set([ws0,ws1]);
      backs.forEach(bk=>{ if(bk.lo>ws0+1e-6&&bk.lo<ws1-1e-6)bps.add(bk.lo); if(bk.hi>ws0+1e-6&&bk.hi<ws1-1e-6)bps.add(bk.hi); });
      const pts=[...bps].sort((p,q)=>p-q);
      const interp=(s)=>{ const den=(sOf(w.wb)-sOf(w.wa))||1, f=(s-sOf(w.wa))/den;
        return { x:w.wa.x+(w.wb.x-w.wa.x)*f, y:w.wa.y+(w.wb.y-w.wa.y)*f }; };
      w.subLoads=[];
      for(let i=0;i<pts.length-1;i++){
        const a0=pts[i], a1=pts[i+1]; if(a1-a0<0.5) continue;
        const mid=(a0+a1)/2; let leePar=0, bestD=-Infinity;
        backs.forEach(bk=>{ if(mid>=bk.lo-1e-6&&mid<=bk.hi+1e-6&&bk.d>bestD){ bestD=bk.d; leePar=bk.par; } });
        const plf = base + LM.lee(pr, leePar);
        L.segs.push({ s0:a0, s1:a1, plf });
        w.subLoads.push({ plf, len:a1-a0, a:interp(a0), b:interp(a1) });   // for the on-plan display
        L.smin=Math.min(L.smin,a0); L.smax=Math.max(L.smax,a1);
      }
    });

    // dashed "tributary" lines wherever the load changes along a line (a real front node OR the
    // projection of a back-wall node), drawn from the windward wall across to the leeward face.
    const divides=[];
    lines.forEach(L=>{
      L.segs.sort((p,q)=>p.s0-q.s0);
      for(let i=0;i<L.segs.length-1;i++){
        const cur=L.segs[i], nxt=L.segs[i+1];
        if(Math.abs(cur.s1-nxt.s0)<0.6 && Math.abs(cur.plf-nxt.plf)>0.5){
          const a=(cur.s1+nxt.s0)/2;
          const Pw = axis==="v" ? {x:a, y:L.depth*sign} : {x:L.depth*sign, y:a};
          divides.push({ x1:Pw.x, y1:Pw.y, x2:Pw.x+travel.x*(alMax-L.depth), y2:Pw.y+travel.y*(alMax-L.depth) });
        }
      }
    });

    // a support shared by several windward lines sums their reactions into ONE arrow
    const agg={}; let baseShear=0;
    lines.forEach(L=>{
      L.segs.forEach(s=> baseShear += s.plf*(s.s1-s.s0)/1000);
      const r=lineReactions(L, graph, isSup, travel, sOf, along);
      if(r.imbalance) anyImbalance=true;
      r.reactions.forEach(rr=>{
        if(!agg[rr.key]) agg[rr.key]={ key:rr.key, kips:0, ax:rr.ax, ay:rr.ay };
        agg[rr.key].kips += rr.kips;
      });
    });
    return { axis, sign, tdir:travel, windLoads:drawn, reactions:Object.values(agg),
             divides, baseShear, imbalance:anyImbalance };
  }
}

// ── STEP 3: 1st-floor (floor diaphragm) load for the MIXED-height case ───────────────────────────
// Additive sibling of buildSecData (the guarded fn is UNTOUCHED). Used ONLY on the 1st-floor view /
// floor-1 design when ≥1 wall is tagged 1-story. A windward wall's floor-diaphragm plf VARIES along
// its length: at each across-wind station it sums the strips connected to the FLOOR diaphragm in its
// downwind shadow —
//   • own ½·H·pw      (the top half of its own wall)
//   • + its OWN parapet IF it is 1-story (a 1-story wall's roof sits at the floor-diaphragm level)
//     — a 2-story windward wall instead adds ½·H₂·pw (bottom half of ITS upper wall; no parapet,
//       whose load belongs to the roof diaphragm)
//   • + ½·H₂·pw of the NEAREST 2-story wall standing behind it (ONE face — its upper wall's bottom
//     half pours into this floor diaphragm; the top half already went to the roof)  ← "the 454"
//   • + leeward parapet of the exterior back wall IF that back wall is 1-story
// Same windward + overlap-shadow + line-grouping + subdivision machinery as buildSecData; reuses
// findLeewardPartner and lineReactions verbatim. isOne(key) = the wall is tagged 1-story.
function buildSecDataF1(section, graph, loop, isSup, propsFor, isOne){
  if(!section) return null;
  const { axis, sign } = section;
  const travel = axis==="v" ? {x:0,y:sign} : {x:sign,y:0};
  const ring = loop?loop.ring:null;
  let cx=0,cy=0,cn=0;
  (ring||graph.nodes).forEach(p=>{cx+=p.x;cy+=p.y;cn++;}); if(cn){cx/=cn;cy/=cn;}
  const extN=(a,b)=>{
    const dx=b.x-a.x, dy=b.y-a.y, len=Math.hypot(dx,dy)||1;
    let nx=-dy/len, ny=dx/len;
    const mx=(a.x+b.x)/2, my=(a.y+b.y)/2;
    if(ring){ if(pointInRing(mx+nx*0.4,my+ny*0.4,ring)){ nx=-nx; ny=-ny; } }
    else { if((mx-cx)*nx+(my-cy)*ny<0){ nx=-nx; ny=-ny; } }
    return {nx,ny,len};
  };
  const windLoads=[];
  for(const e of graph.edges){
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    if(!a||!b) continue;
    const wallAxis=edgeAxis(a,b);
    if(axis==="v" ? wallAxis!=="h" : wallAxis!=="v") continue;
    const {nx,ny,len}=extN(a,b);
    if(nx*travel.x + ny*travel.y >= -1e-6) continue;
    windLoads.push({ wa:a, wb:b, nx, ny, len, key:keyOf(e) });
  }
  const along=(p)=> p.x*travel.x + p.y*travel.y;
  const tran =(p)=> -p.y*travel.x + p.x*travel.y;
  const ov=(a0,a1,b0,b1)=> Math.min(Math.max(a0,a1),Math.max(b0,b1)) - Math.max(Math.min(a0,a1),Math.min(b0,b1));
  const kept = windLoads.filter(w=>{
    const wa0=tran(w.wa), wa1=tran(w.wb), aw=along({x:(w.wa.x+w.wb.x)/2,y:(w.wa.y+w.wb.y)/2});
    const overlapShadow = windLoads.some(u=>{
      if(u===w) return false;
      const au=along({x:(u.wa.x+u.wb.x)/2,y:(u.wa.y+u.wb.y)/2});
      return au < aw-0.5 && ov(wa0,wa1,tran(u.wa),tran(u.wb)) > 0.5;
    });
    return !overlapShadow;
  });
  let anyImbalance=false;
  const sOf =(p)=> axis==="v" ? p.x : p.y;
  const recv = axis==="v" ? "h" : "v";
  // a windward wall's OWN floor-diaphragm contribution (no leeward parapet / no accumulation yet)
  const baseOf=(key)=>{
    const pr=propsFor(key); const half=0.5*(pr.H||0)*(pr.pw||0);
    const val = isOne(key) ? half + (pr.par||0)*(pr.qWind||0)   // 1-story: + own parapet (floor-level roof)
                           : half + 0.5*(pr.H2||0)*(pr.pw||0);  // 2-story: + bottom half of its own upper wall
    return { val, pr };
  };
  kept.forEach(w=>{
    const {val,pr}=baseOf(w.key);
    const cLee=findLeewardPartner(w.key, axis, sign, graph);
    const cPar=(cLee && isOne(cLee)) ? (propsFor(cLee).par||0) : 0;   // leeward parapet only if back wall is 1-story
    w.total = val + cPar*(pr.qLee||0);
    w.tdir=travel;
  });
  const drawn = kept.filter(w=>w.total>0);
  let alMin=Infinity, alMax=-Infinity;
  graph.nodes.forEach(p=>{ const al=along(p); if(al<alMin)alMin=al; if(al>alMax)alMax=al; });
  const lines=[];
  drawn.forEach(w=>{
    const depth=(along(w.wa)+along(w.wb))/2;
    let L=lines.find(l=>Math.abs(l.depth-depth)<0.6);
    if(!L){ L={depth, segs:[], smin:Infinity, smax:-Infinity}; lines.push(L); }
    const ws0=Math.min(sOf(w.wa),sOf(w.wb)), ws1=Math.max(sOf(w.wa),sOf(w.wb));
    const {val:base, pr}=baseOf(w.key);
    // back walls overlapping this windward wall (downwind): parapet (leeward, only if 1-story) +
    // the ½·H₂·pw accumulation (only if 2-story) + depth d.
    const backs=[];
    for(const e of graph.edges){
      if(keyOf(e)===w.key) continue;
      const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b); if(!a||!b) continue;
      if(edgeAxis(a,b)!==recv) continue;
      const d=(along(a)+along(b))/2; if(d<=depth+0.6) continue;
      const lo=Math.max(ws0,Math.min(sOf(a),sOf(b))), hi=Math.min(ws1,Math.max(sOf(a),sOf(b)));
      if(hi-lo>0.5){
        const bp=propsFor(keyOf(e)), one=isOne(keyOf(e));
        backs.push({ lo, hi, d,
                     par: one ? (bp.par||0) : 0,                  // → floor diaphragm only if 1-story
                     h2:  one ? 0 : 0.5*(bp.H2||0)*(bp.pw||0) }); // ½·H₂·pw accumulation only if 2-story
      }
    }
    const bps=new Set([ws0,ws1]);
    backs.forEach(bk=>{ if(bk.lo>ws0+1e-6&&bk.lo<ws1-1e-6)bps.add(bk.lo); if(bk.hi>ws0+1e-6&&bk.hi<ws1-1e-6)bps.add(bk.hi); });
    const pts=[...bps].sort((p,q)=>p-q);
    const interp=(s)=>{ const den=(sOf(w.wb)-sOf(w.wa))||1, f=(s-sOf(w.wa))/den;
      return { x:w.wa.x+(w.wb.x-w.wa.x)*f, y:w.wa.y+(w.wb.y-w.wa.y)*f }; };
    w.subLoads=[];
    for(let i=0;i<pts.length-1;i++){
      const a0=pts[i], a1=pts[i+1]; if(a1-a0<0.5) continue;
      const mid=(a0+a1)/2;
      let leePar=0, bestD=-Infinity;                                   // exterior (farthest) back parapet
      backs.forEach(bk=>{ if(mid>=bk.lo-1e-6&&mid<=bk.hi+1e-6&&bk.d>bestD){ bestD=bk.d; leePar=bk.par; } });
      let acc=0, nearD=Infinity;                                       // NEAREST 2-story back → one face
      backs.forEach(bk=>{ if(bk.h2>0&&mid>=bk.lo-1e-6&&mid<=bk.hi+1e-6&&bk.d<nearD){ nearD=bk.d; acc=bk.h2; } });
      const plf = base + leePar*(pr.qLee||0) + acc;
      L.segs.push({ s0:a0, s1:a1, plf });
      w.subLoads.push({ plf, len:a1-a0, a:interp(a0), b:interp(a1) });
      L.smin=Math.min(L.smin,a0); L.smax=Math.max(L.smax,a1);
    }
  });
  const divides=[];
  lines.forEach(L=>{
    L.segs.sort((p,q)=>p.s0-q.s0);
    for(let i=0;i<L.segs.length-1;i++){
      const cur=L.segs[i], nxt=L.segs[i+1];
      if(Math.abs(cur.s1-nxt.s0)<0.6 && Math.abs(cur.plf-nxt.plf)>0.5){
        const a=(cur.s1+nxt.s0)/2;
        const Pw = axis==="v" ? {x:a, y:L.depth*sign} : {x:L.depth*sign, y:a};
        divides.push({ x1:Pw.x, y1:Pw.y, x2:Pw.x+travel.x*(alMax-L.depth), y2:Pw.y+travel.y*(alMax-L.depth) });
      }
    }
  });
  const agg={}; let baseShear=0;
  lines.forEach(L=>{
    L.segs.forEach(s=> baseShear += s.plf*(s.s1-s.s0)/1000);
    const r=lineReactions(L, graph, isSup, travel, sOf, along);
    if(r.imbalance) anyImbalance=true;
    r.reactions.forEach(rr=>{
      if(!agg[rr.key]) agg[rr.key]={ key:rr.key, kips:0, ax:rr.ax, ay:rr.ay };
      agg[rr.key].kips += rr.kips;
    });
  });
  return { axis, sign, tdir:travel, windLoads:drawn, reactions:Object.values(agg),
           divides, baseShear, imbalance:anyImbalance };
}

// ── styles ─────────────────────────────────────────────────────────────────
const CSS = `
.r{ --bg:#EFEDE6;--panel:#FFFFFF;--line:#D8D4C8;--ink:#1C2733;--muted:#586470;--accent:#23577F;--hot:#9A6B1F;--pink:#B23A2A;
  font-family:'IBM Plex Mono',ui-monospace,'SF Mono',Menlo,Consolas,monospace;color:var(--ink);
  background-color:var(--bg);
  background-image:
    linear-gradient(rgba(35,87,127,.12) 1px, transparent 1px),
    linear-gradient(90deg, rgba(35,87,127,.12) 1px, transparent 1px),
    linear-gradient(rgba(35,87,127,.06) 1px, transparent 1px),
    linear-gradient(90deg, rgba(35,87,127,.06) 1px, transparent 1px);
  background-size:110px 110px, 110px 110px, 22px 22px, 22px 22px;
  min-height:100%;box-sizing:border-box;padding:18px; }
.r *{box-sizing:border-box;}
.hd{display:flex;align-items:baseline;gap:12px;flex-wrap:wrap;margin-bottom:14px;}
.htitle{font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;font-weight:800;font-size:19px;letter-spacing:.01em;margin:0;color:var(--ink);}
.htag{font-size:11px;color:var(--muted);}
.layout{display:grid;grid-template-columns:1fr;gap:14px;}
@media(min-width:760px){.layout{grid-template-columns:1fr 248px;}}
.stage{position:relative;border:1.5px solid var(--ink);border-radius:0;overflow:hidden;
  background:#FFFFFF;
  box-shadow:0 1px 1px rgba(28,39,51,.04), 0 10px 24px -14px rgba(28,39,51,.30), 4px 4px 0 rgba(28,39,51,.10);
  animation:rise .5s ease both;}
@keyframes rise{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
.cvs{display:block;width:100%;height:auto;touch-action:none;cursor:crosshair;background:#FFFFFF;border-radius:0;}
.panel{display:flex;flex-direction:column;gap:12px;}
.card{border:1px solid var(--line);border-radius:4px;background:var(--panel);padding:12px 13px;}
.card h4{margin:0 0 9px;font-size:10.5px;letter-spacing:.14em;text-transform:uppercase;color:var(--accent);font-weight:700;}
.row{display:flex;justify-content:space-between;align-items:baseline;padding:3px 0;}
.row span{color:var(--muted);font-size:12px;}
.row b{font-weight:600;font-size:14px;font-variant-numeric:tabular-nums;}
.row b small{color:var(--muted);font-weight:400;font-size:11px;margin-left:3px;}
.brow{display:flex;flex-wrap:wrap;gap:6px;}
.btn{font-family:inherit;font-size:11.5px;color:var(--ink);cursor:pointer;
  background:#FFFFFF;border:1px solid var(--line);border-radius:4px;padding:6px 9px;
  transition:.15s;flex:1 1 auto;min-width:60px;text-align:center;}
.btn:hover{border-color:var(--accent);color:var(--accent);background:#E8EFF4;}
.btn:disabled{opacity:.35;cursor:default;}
.btn.pink:hover{border-color:var(--pink);color:var(--pink);background:#F8E9E5;}
.tog{display:flex;align-items:center;justify-content:space-between;padding:5px 0;font-size:12px;color:var(--muted);cursor:pointer;user-select:none;}
.sw{width:34px;height:19px;border-radius:99px;background:#EDEBE3;border:1px solid var(--line);position:relative;transition:.18s;flex:none;}
.sw.on{background:var(--accent);}
.sw i{position:absolute;top:1.5px;left:1.5px;width:14px;height:14px;border-radius:50%;background:#FFFFFF;transition:.18s;box-shadow:0 1px 2px rgba(28,39,51,.25);}
.sw.on i{left:16px;background:#FFFFFF;}
.hint{font-size:11px;color:var(--muted);line-height:1.6;}
.hint b{color:var(--accent);font-weight:600;}
.cmenu{position:absolute;z-index:30;min-width:148px;background:#FFFFFF;
  border:1px solid var(--line);border-radius:4px;padding:5px;
  box-shadow:0 12px 32px -8px rgba(28,39,51,.28);display:flex;flex-direction:column;gap:2px;animation:pop .12s ease;}
@keyframes pop{from{opacity:0;transform:scale(.96)}to{opacity:1;transform:none}}
.cmh{font-size:10px;letter-spacing:.07em;text-transform:uppercase;color:var(--muted);padding:5px 8px 3px;}
.cmi{font-family:inherit;font-size:12px;text-align:left;color:var(--ink);background:transparent;
  border:0;border-radius:3px;padding:7px 8px;cursor:pointer;width:100%;
  display:flex;align-items:center;gap:8px;justify-content:space-between;}
.cmi:hover{background:#E8EFF4;color:var(--accent);}
.cmi.del:hover{background:#F8E9E5;color:var(--pink);}
.cmi.act{background:#E8EFF4;color:var(--accent);font-weight:600;}
.cmlbl{flex:1 1 auto;}
.cmck{flex:0 0 auto;color:var(--accent);font-weight:700;}
.cmzoom:hover{background:#E8EFF4;color:var(--accent);}
.cmlight{flex:0 0 auto;width:9px;height:9px;border-radius:50%;background:#C9D2DA;
  box-shadow:inset 0 0 0 1px rgba(28,39,51,.18);transition:background .15s ease,box-shadow .15s ease;}
.cmlight.on{background:#34C759;box-shadow:0 0 0 1px rgba(52,199,89,.30),0 0 6px rgba(52,199,89,.65);}
.ribbon{display:flex;align-items:stretch;gap:10px;padding:6px 10px;margin:0 0 10px;border:1px solid var(--line);
  border-radius:4px;background:var(--panel);overflow-x:auto;
  position:sticky;top:var(--tabbar-h,42px);z-index:30;box-shadow:0 2px 10px -7px rgba(28,39,51,.35);}
.rgroup{display:flex;flex-direction:column;gap:3px;}
.rlabel{font-size:10.5px;letter-spacing:.14em;text-transform:uppercase;color:var(--muted);padding-left:2px;}
@media print{ .r{background-image:none;background-color:#FFF;} .ribbon{box-shadow:none;} }
.rbtns{display:flex;gap:4px;}
.rbtn{border:1px solid var(--line);background:#FFFFFF;color:var(--ink);font-size:11.5px;font-weight:600;
  padding:5px 9px;border-radius:4px;cursor:pointer;white-space:nowrap;
  transition:border-color .14s ease,color .14s ease,background .14s ease,box-shadow .14s ease;}
.rbtn:hover{border-color:var(--accent);color:var(--accent);background:#F6F9FB;}
.rbtn:active{box-shadow:inset 0 1px 3px rgba(28,39,51,.18);}
.rbtn.ron{background:#E8EFF4;border-color:var(--accent);color:var(--accent);}
.rbtn.raccent{border-color:var(--accent);color:var(--accent);}
/* (rev 153) rprimary = the ONE elevated primary action per tab: a filled accent button so the
   eye lands on the next step, vs. the many equal-weight outline buttons. Defined AFTER .raccent so
   it wins on equal specificity. A stale STALE_BTN inline style still overrides it (amber > primary). */
.rbtn.rprimary{border-color:var(--accent);background:var(--accent);color:#FFFFFF;}
.rbtn.rprimary:hover{background:#1B466A;border-color:#1B466A;color:#FFFFFF;}
.rbtn:disabled{opacity:.35;cursor:default;border-color:var(--line);color:var(--muted);}
.rsel{border:1px solid var(--line);background:#FFFFFF;color:var(--ink);font-size:11.5px;font-weight:600;
  padding:5px 8px;border-radius:4px;cursor:pointer;white-space:nowrap;font-family:inherit;
  transition:border-color .14s ease,color .14s ease,background .14s ease;}
.rsel:hover{border-color:var(--accent);color:var(--accent);background:#F6F9FB;}
.rsel:focus{outline:none;border-color:var(--accent);box-shadow:0 0 0 2px rgba(35,87,127,.15);}
.rsep{width:1px;background:linear-gradient(180deg,transparent,var(--line) 22%,var(--line) 78%,transparent);margin:0;}
.statusbar{display:flex;align-items:center;gap:14px;margin-top:8px;padding:5px 12px;border:1px solid var(--line);
  border-radius:4px;background:var(--panel);font-size:11px;color:var(--muted);
  font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;}
.stcoord{min-width:150px;color:var(--ink);}
.stmode{font-weight:700;color:var(--muted);}
.stmode.draw{color:var(--accent);}
.stmode.pan{color:var(--accent);}
.stflag{cursor:pointer;letter-spacing:.08em;opacity:.45;}
.stflag.on{opacity:1;color:var(--accent);font-weight:700;}
.stright{margin-left:auto;}
/* Sliding 1-Story / 2-Story pill (ribbon) — segmented control with a white thumb that slides. */
.storypill{position:relative;display:grid;grid-template-columns:1fr 1fr;background:var(--accent);
  border-radius:99px;cursor:pointer;user-select:none;box-shadow:inset 0 1px 3px rgba(28,39,51,.25);}
.storythumb{position:absolute;top:3px;bottom:3px;left:3px;width:calc(50% - 3px);
  background:#FFFFFF;border-radius:99px;box-shadow:0 1px 2px rgba(28,39,51,.3);
  transition:transform .22s cubic-bezier(.4,0,.2,1);}
.storypill.two .storythumb{transform:translateX(100%);}
.storyopt{position:relative;z-index:1;border:0;background:transparent;font-family:inherit;
  font-size:11px;font-weight:700;letter-spacing:.02em;padding:5px 14px;cursor:pointer;
  color:#FFFFFF;transition:color .2s ease;white-space:nowrap;text-align:center;}
.storyopt.on{color:var(--accent);}
/* Floor selector — its own bar directly BELOW the drawing area (never over the canvas, so clicks land). */
.canvascol{display:flex;flex-direction:column;min-width:0;}
.floorbar{display:flex;justify-content:center;margin-bottom:8px;}   /* rev 64: switcher moved ABOVE the canvas */
.floorsel{display:inline-flex;border:1.5px solid var(--ink);border-radius:4px;overflow:hidden;background:#FFFFFF;
  box-shadow:4px 4px 0 rgba(28,39,51,.10);font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;}
.floorbar.off .floorsel{opacity:.5;border-color:var(--line);box-shadow:none;}
.floortab{border:0;background:#FFFFFF;color:var(--muted);font-size:11px;font-weight:600;letter-spacing:.03em;
  padding:5px 14px;cursor:pointer;transition:background .14s ease,color .14s ease;}
.floortab+.floortab{border-left:1px solid var(--line);}
.floortab:hover:not(:disabled){background:#F6F9FB;color:var(--accent);}
.floortab.act{background:var(--accent);color:#FFFFFF;}
.floortab:disabled{cursor:default;}
.floorbar.off .floortab.act{background:#EDEBE3;color:var(--muted);}
/* Floor badge — top-left of the canvas (2-story mode); pointer-events:none so it never blocks the SVG. */
.floorbadge{position:absolute;top:8px;left:8px;z-index:4;pointer-events:none;
  background:rgba(35,87,127,.92);color:#FFFFFF;font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;
  font-size:11px;font-weight:700;letter-spacing:.08em;text-transform:uppercase;
  padding:4px 9px;border-radius:3px;box-shadow:0 2px 6px -2px rgba(28,39,51,.4);}
.floorbadge span{font-weight:500;opacity:.78;}
.allonestory-warn{position:absolute;top:8px;right:8px;z-index:5;pointer-events:none;max-width:62%;
  background:rgba(154,107,31,.95);color:#FFFFFF;font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;
  font-size:11px;font-weight:600;letter-spacing:.02em;line-height:1.3;
  padding:5px 10px;border-radius:3px;box-shadow:0 2px 6px -2px rgba(28,39,51,.4);}
/* (rev 68) one-time "stray edge healed on load" toast — top-center, click to dismiss, auto-clears. */
.healtoast{position:absolute;top:8px;left:50%;transform:translateX(-50%);z-index:6;cursor:pointer;max-width:80%;
  background:rgba(34,108,74,.96);color:#FFFFFF;font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;
  font-size:11px;font-weight:700;letter-spacing:.02em;line-height:1.3;
  padding:5px 11px;border-radius:3px;box-shadow:0 2px 6px -2px rgba(28,39,51,.4);}
.healtoast span{font-weight:500;opacity:.85;}
.h2row{border:1px solid var(--line);border-left:3px solid var(--accent);border-radius:4px;padding:9px 11px;margin-bottom:12px;background:#F6F9FB;}
.h2top{display:flex;align-items:center;justify-content:space-between;gap:10px;}
.h2top label{font-size:12px;font-weight:600;color:var(--ink);}
.h2inp{display:flex;align-items:center;gap:4px;background:#FFFFFF;border:1.5px solid var(--accent);border-radius:4px;padding:3px 8px;}
.h2inp input{font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;font-size:14px;font-weight:700;color:var(--accent);
  background:transparent;border:0;outline:none;width:56px;text-align:right;}
.h2inp span{font-size:11px;color:var(--muted);}
.h2hint{font-size:10.5px;color:var(--muted);line-height:1.5;margin-top:6px;}
.dim-input-wrap{position:absolute;transform:translate(-50%,-50%);z-index:25;display:flex;align-items:center;gap:3px;
  background:#FFFFFF;border:1.5px solid var(--hot);border-radius:4px;padding:4px 7px;box-shadow:0 8px 24px -6px rgba(28,39,51,.3);animation:pop .1s ease;}
.dim-inp{font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;font-size:13px;color:var(--hot);background:transparent;border:0;outline:none;width:52px;text-align:right;font-weight:700;}
.dim-unit{font-size:11px;color:var(--muted);}
/* wind window modal */
.ovl{position:fixed;inset:0;z-index:60;background:rgba(28,39,51,.35);display:flex;align-items:center;justify-content:center;padding:14px;animation:pop .14s ease;}
.win{width:min(580px,97vw);max-height:94vh;overflow:auto;background:#FFFFFF;border:1.5px solid var(--ink);border-radius:0;box-shadow:6px 6px 0 rgba(28,39,51,.15);}
.win-h{display:flex;align-items:center;justify-content:space-between;padding:13px 16px;border-bottom:1.5px solid var(--ink);position:sticky;top:0;background:#FFFFFF;z-index:2;}
.win-t{font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;font-weight:800;font-size:15px;color:var(--ink);}
.win-x{background:#FFFFFF;border:1px solid var(--line);color:var(--ink);border-radius:4px;width:30px;height:30px;cursor:pointer;font-size:16px;line-height:1;}
.win-x:hover{border-color:var(--pink);color:var(--pink);}
.win-b{padding:14px 16px;}
.seg{border:1px solid var(--line);border-radius:4px;padding:11px 12px;margin-bottom:10px;background:#FFFFFF;}
.seg h5{margin:0 0 9px;font-size:10px;letter-spacing:.14em;text-transform:uppercase;font-weight:700;}
.seg.wall h5{color:var(--accent);} .seg.par h5{color:var(--hot);}
.fgrid{display:grid;grid-template-columns:1fr 1fr;gap:9px;}
.fld{display:flex;flex-direction:column;gap:3px;}
.fld label{font-size:10.5px;color:var(--muted);letter-spacing:.06em;text-transform:uppercase;}
.fld input{font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;font-size:13px;color:var(--accent);font-weight:600;background:#FDFDFB;border:1px solid var(--line);border-radius:4px;padding:7px 9px;outline:none;}
.fld input:focus{border-color:var(--accent);}
.rev{font-family:inherit;font-size:12px;color:var(--ink);background:#FFFFFF;border:1px solid var(--line);border-radius:4px;padding:9px 12px;cursor:pointer;display:flex;align-items:center;justify-content:center;gap:8px;width:100%;}
.rev:hover{border-color:var(--pink);color:var(--pink);background:#F8E9E5;}
.tot{margin-top:4px;background:#E8EFF4;border:1px solid var(--line);border-radius:4px;padding:14px 16px;}
.tot .lbl{font-size:10px;letter-spacing:.08em;text-transform:uppercase;color:var(--muted);}
.tot .v{font-family:'IBM Plex Mono',ui-monospace,Menlo,monospace;font-size:30px;font-weight:600;line-height:1.1;margin-top:3px;color:var(--accent);}
.tot .v small{font-size:15px;color:var(--muted);font-weight:400;}
.brk{display:flex;justify-content:space-between;font-size:11.5px;color:var(--muted);padding:2px 0;font-variant-numeric:tabular-nums;}
.brk b{color:var(--ink);font-weight:500;}
`;

/* ═══════════════ SECTION ELEVATION DIAGRAM ═══════════════ */
function SecDiagram({ v, upd }) {
  const [edit,setEdit]=useState(null);   // {field,prop,l,t}
  const num=s=>Math.max(0,parseFloat(s)||0);
  const HL=num(v.H), HR=num(v.leeH), pw=num(v.pw), parW=num(v.wH), qW=num(v.wQ), parL=num(v.lH), qL=num(v.lQ);
  const VBW=330, VBH=250, padTop=18, padBot=20, availH=VBH-padTop-padBot;
  // scale to the taller side-stack (wall + its own parapet) so a sloping roof + both parapets fit;
  // identical to the old flat-roof scaling when HL===HR.
  const maxFt=Math.max(HL+parW, HR+parL, 1), pxPerFt=availH/maxFt;
  const wallBot=padTop+availH;                          // common foundation baseline (both walls)
  const wallLX=95, wallRX=250;
  const roofYL=wallBot - HL*pxPerFt;                    // windward roof point (left,  height HL)
  const roofYR=wallBot - HR*pxPerFt;                    // leeward  roof point (right, height HR)
  const parWTop=roofYL - parW*pxPerFt, parLTop=roofYR - parL*pxPerFt;
  const maxPsf=Math.max(pw,qW,qL,1), aS=42/maxPsf;
  const aWall=pw>0?Math.max(pw*aS,6):0, aWind=qW>0?Math.max(qW*aS,6):0, aLee=qL>0?Math.max(qL*aS,6):0;
  const rows=(yTop,yBot)=>{ const n=Math.max(1,Math.round((yBot-yTop)/8)); return Array.from({length:n+1},(_,i)=>yTop+(yBot-yTop)*i/n); };
  const CY="#23577F", YEL="#1C2733";
  const open=(field,prop,cx,cy)=>setEdit({field,prop,l:cx/VBW*100,t:cy/VBH*100});
  const Box=({cx,cy,text,color,field,prop,rot=0})=>{
    const w=text.length*4.1+6, h=11;
    return (
      <g style={{cursor:"pointer"}} onClick={()=>open(field,prop,cx,cy)} transform={rot?`rotate(${rot},${cx},${cy})`:undefined}>
        <rect x={cx-w/2} y={cy-h/2} width={w} height={h} rx={1.5} fill={color}/>
        <text x={cx} y={cy+0.4} fill="#fff" fontSize={7} fontWeight={700} textAnchor="middle" dominantBaseline="middle" style={{userSelect:"none"}}>{text}</text>
      </g>
    );
  };
  const wMid=(parWTop+roofYL)/2, hMidL=(roofYL+wallBot)/2, hMidR=(roofYR+wallBot)/2, lMid=(parLTop+roofYR)/2;
  const roofMidX=(wallLX+wallRX)/2, roofMidY=(roofYL+roofYR)/2;
  const roofAng=Math.atan2(roofYR-roofYL, wallRX-wallLX)*180/Math.PI;   // 0 when flat
  return (
    <div style={{position:"relative"}}>
      <svg viewBox={`0 0 ${VBW} ${VBH}`} style={{width:"100%",height:"auto",display:"block"}}>
        <defs>
          <marker id="dArr" markerWidth="6" markerHeight="6" refX="4.6" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6 Z" fill={CY}/></marker>
        </defs>
        <rect x="0" y="0" width={VBW} height={VBH} fill={C_BG} rx="6"/>

        {/* WALL SECTION — trapezoid: left edge = windward height, right edge = leeward height, top = roof line (slopes when heights differ) */}
        <polygon points={`${wallLX},${roofYL} ${wallRX},${roofYR} ${wallRX},${wallBot} ${wallLX},${wallBot}`} fill="none" stroke={YEL} strokeWidth="1.4"/>
        <text x={roofMidX} y={roofMidY-3} fill="#6B7684" fontSize="7" letterSpacing=".25em" textAnchor="middle"
              transform={`rotate(${roofAng},${roofMidX},${roofMidY})`}>ROOF LINE</text>

        {/* parapet walls — a single line rising from each side's own roof point (continues the wall face up) */}
        {parW>0 && <line x1={wallLX} y1={roofYL} x2={wallLX} y2={parWTop} stroke={YEL} strokeWidth="1.4"/>}
        {parL>0 && <line x1={wallRX} y1={roofYR} x2={wallRX} y2={parLTop} stroke={YEL} strokeWidth="1.4"/>}
        {/* node where each parapet starts (top of wall / roof point) — repositions live as heights are typed */}
        {parW>0 && <circle cx={wallLX} cy={roofYL} r="2.4" fill={C_NODE} stroke="#FFFFFF" strokeWidth="1"/>}
        {parL>0 && <circle cx={wallRX} cy={roofYR} r="2.4" fill={C_NODE} stroke="#FFFFFF" strokeWidth="1"/>}

        {/* windward WALL pressure — left edge, arrows point right */}
        {HL>0&&pw>0&&<g>
          <line x1={wallLX-aWall} y1={roofYL} x2={wallLX-aWall} y2={wallBot} stroke={CY} strokeWidth="1"/>
          {rows(roofYL,wallBot).map((y,i)=><line key={i} x1={wallLX-aWall} y1={y} x2={wallLX} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr)"/>)}
        </g>}
        {/* windward PARAPET pressure — left, arrows point right */}
        {parW>0&&qW>0&&<g>
          <line x1={wallLX-aWind} y1={parWTop} x2={wallLX-aWind} y2={roofYL} stroke={CY} strokeWidth="1"/>
          {rows(parWTop,roofYL).map((y,i)=><line key={i} x1={wallLX-aWind} y1={y} x2={wallLX} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr)"/>)}
        </g>}
        {/* leeward PARAPET pressure — right edge, arrows point right (left→right, with the wind) */}
        {parL>0&&qL>0&&<g>
          <line x1={wallRX} y1={parLTop} x2={wallRX} y2={roofYR} stroke={CY} strokeWidth="1"/>
          {rows(parLTop,roofYR).map((y,i)=><line key={i} x1={wallRX} y1={y} x2={wallRX+aLee} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr)"/>)}
        </g>}

        {/* WINDWARD / LEEWARD labels — vertical, beside each parapet line */}
        {parW>0&&<text x={wallLX+8} y={wMid} fill="#6B7684" fontSize="6" letterSpacing=".12em"
              textAnchor="middle" transform={`rotate(-90,${wallLX+8},${wMid})`}>WINDWARD</text>}
        {parL>0&&<text x={wallRX-8} y={lMid} fill="#6B7684" fontSize="6" letterSpacing=".12em"
              textAnchor="middle" transform={`rotate(-90,${wallRX-8},${lMid})`}>LEEWARD</text>}

        {/* pressure boxes (blue, vertical, over the arrows) */}
        <Box cx={wallLX-aWind/2} cy={wMid} text={`${fmt1(qW)} psf`} color={C_DIMBOX} field="wQ" prop="qWind" rot={-90}/>
        <Box cx={wallLX-aWall/2} cy={hMidL} text={`${fmt1(pw)} psf`} color={C_DIMBOX} field="pw" prop="pw"   rot={-90}/>
        <Box cx={wallRX+aLee/2} cy={lMid} text={`${fmt1(qL)} psf`} color={C_DIMBOX} field="lQ" prop="qLee" rot={-90}/>
        {/* height boxes (red, horizontal, beside each element) — windward wall HL, leeward wall HR, both parapets */}
        <Box cx={wallLX+30} cy={wMid} text={`${fmt1(parW)} ft`} color={C_REACTBOX} field="wH"   prop="parW"/>
        <Box cx={wallLX+22}      cy={hMidL} text={`${fmt1(HL)} ft`}  color={C_REACTBOX} field="H"    prop="H"/>
        <Box cx={wallRX-22}      cy={hMidR} text={`${fmt1(HR)} ft`}  color={C_REACTBOX} field="leeH" prop="leeH"/>
        <Box cx={wallRX-30} cy={lMid} text={`${fmt1(parL)} ft`} color={C_REACTBOX} field="lH"   prop="parL"/>
      </svg>

      {edit && (
        <input autoFocus type="number" inputMode="decimal" value={v[edit.field] ?? ""}
          onChange={upd(edit.field, edit.prop)} onBlur={()=>setEdit(null)}
          onKeyDown={e=>{ if(e.key==="Enter"||e.key==="Escape") setEdit(null); }}
          style={{ position:"absolute", left:`${edit.l}%`, top:`${edit.t}%`, transform:"translate(-50%,-50%)",
                   width:58, padding:"4px 6px", textAlign:"center",
                   background:"#FFFFFF", color:"#9A6B1F", border:"1.5px solid #9A6B1F", borderRadius:3, font:"700 13px ui-monospace,Menlo,monospace", outline:"none", zIndex:6 }}/>
      )}
    </div>
  );
}

/* ═══════════════ TWO-STORY SECTION ELEVATION (Step 4) ═══════════════
   Stacked flat-roof elevation: 1st story (H) + 2nd story (H₂) split by the 2nd-floor diaphragm,
   parapets on top, windward wall pressure over both stories, and both diaphragm line-load callouts.
   SecDiagram (1-story) is left untouched; the wind window picks this variant in 2-story mode. */
function SecDiagram2({ v, upd, roofLL, floorLL }) {
  const [edit,setEdit]=useState(null);
  const num=s=>Math.max(0,parseFloat(s)||0);
  const H1=num(v.H),   H2=num(v.H2),   pw=num(v.pw), parW=num(v.wH), qW=num(v.wQ);   // windward 1st/2nd-story + parapet
  const LH1=num(v.leeH), LH2=num(v.leeH2),            parL=num(v.lH), qL=num(v.lQ);   // leeward  1st/2nd-story + parapet
  const VBW=362, VBH=300, padTop=22, padBot=26, availH=VBH-padTop-padBot;
  const maxFt=Math.max(H1+H2+parW, LH1+LH2+parL, 1), pxPerFt=availH/maxFt;
  const wallBot=padTop+availH;                          // 1st floor / foundation baseline (shared)
  const wallLX=106, wallRX=236;
  const yF2L=wallBot - H1*pxPerFt,  yRoofL=yF2L - H2*pxPerFt;    // windward 2nd-floor + roof points
  const yF2R=wallBot - LH1*pxPerFt, yRoofR=yF2R - LH2*pxPerFt;   // leeward  2nd-floor + roof points (may differ → sloped)
  const parWTop=yRoofL - parW*pxPerFt, parLTop=yRoofR - parL*pxPerFt;
  const maxPsf=Math.max(pw,qW,qL,1), aS=40/maxPsf;
  const aWall=pw>0?Math.max(pw*aS,6):0, aWind=qW>0?Math.max(qW*aS,6):0, aLee=qL>0?Math.max(qL*aS,6):0;
  const rows=(yTop,yBot)=>{ const n=Math.max(1,Math.round((yBot-yTop)/8)); return Array.from({length:n+1},(_,i)=>yTop+(yBot-yTop)*i/n); };
  const CY="#23577F", YEL="#1C2733", GOLD="#9A6B1F";
  const open=(field,prop,cx,cy)=>setEdit({field,prop,l:cx/VBW*100,t:cy/VBH*100});
  const Box=({cx,cy,text,color,field,prop,rot=0})=>{
    const w=text.length*4.1+6, h=11;
    return (
      <g style={{cursor:"pointer"}} onClick={()=>open(field,prop,cx,cy)} transform={rot?`rotate(${rot},${cx},${cy})`:undefined}>
        <rect x={cx-w/2} y={cy-h/2} width={w} height={h} rx={1.5} fill={color}/>
        <text x={cx} y={cy+0.4} fill="#fff" fontSize={7} fontWeight={700} textAnchor="middle" dominantBaseline="middle" style={{userSelect:"none"}}>{text}</text>
      </g>
    );
  };
  const mid2L=(yRoofL+yF2L)/2, mid1L=(yF2L+wallBot)/2;          // windward story mids (left height boxes)
  const mid2R=(yRoofR+yF2R)/2, mid1R=(yF2R+wallBot)/2;          // leeward  story mids (right height boxes)
  const wMid=(parWTop+yRoofL)/2, lMid=(parLTop+yRoofR)/2;
  const cx=(wallLX+wallRX)/2, calloutX=VBW-90;
  const lblY2=(mid2L+mid2R)/2, lblY1=(mid1L+mid1R)/2;          // story labels centered between the (possibly sloped) lines
  return (
    <div style={{position:"relative"}}>
      <svg viewBox={`0 0 ${VBW} ${VBH}`} style={{width:"100%",height:"auto",display:"block"}}>
        <defs>
          <marker id="dArr2" markerWidth="6" markerHeight="6" refX="4.6" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6 Z" fill={CY}/></marker>
        </defs>
        <rect x="0" y="0" width={VBW} height={VBH} fill={C_BG} rx="6"/>

        {/* building outline — two stories; roof & 2nd-floor lines slope if windward/leeward heights differ */}
        <line x1={wallLX} y1={yRoofL} x2={wallLX} y2={wallBot} stroke={YEL} strokeWidth="1.4"/>
        <line x1={wallRX} y1={yRoofR} x2={wallRX} y2={wallBot} stroke={YEL} strokeWidth="1.4"/>
        <line x1={wallLX} y1={wallBot} x2={wallRX} y2={wallBot} stroke={YEL} strokeWidth="1.4"/>
        <line x1={wallLX} y1={yRoofL} x2={wallRX} y2={yRoofR} stroke={YEL} strokeWidth="1.4"/>{/* roof diaphragm */}
        <line x1={wallLX} y1={yF2L}   x2={wallRX} y2={yF2R}   stroke={YEL} strokeWidth="1.1" strokeDasharray="4 3"/>{/* 2nd-floor diaphragm */}

        {/* parapets */}
        {parW>0 && <line x1={wallLX} y1={yRoofL} x2={wallLX} y2={parWTop} stroke={YEL} strokeWidth="1.4"/>}
        {parL>0 && <line x1={wallRX} y1={yRoofR} x2={wallRX} y2={parLTop} stroke={YEL} strokeWidth="1.4"/>}
        {parW>0 && <circle cx={wallLX} cy={yRoofL} r="2.2" fill={C_NODE} stroke="#FFFFFF" strokeWidth="1"/>}
        {parL>0 && <circle cx={wallRX} cy={yRoofR} r="2.2" fill={C_NODE} stroke="#FFFFFF" strokeWidth="1"/>}

        {/* windward WALL pressure — both stories, arrows point right */}
        {pw>0&&(H1+H2)>0&&<g>
          <line x1={wallLX-aWall} y1={yRoofL} x2={wallLX-aWall} y2={wallBot} stroke={CY} strokeWidth="1"/>
          {rows(yRoofL,wallBot).map((y,i)=><line key={i} x1={wallLX-aWall} y1={y} x2={wallLX} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr2)"/>)}
        </g>}
        {/* windward PARAPET pressure */}
        {parW>0&&qW>0&&<g>
          <line x1={wallLX-aWind} y1={parWTop} x2={wallLX-aWind} y2={yRoofL} stroke={CY} strokeWidth="1"/>
          {rows(parWTop,yRoofL).map((y,i)=><line key={i} x1={wallLX-aWind} y1={y} x2={wallLX} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr2)"/>)}
        </g>}
        {/* leeward PARAPET pressure — right side */}
        {parL>0&&qL>0&&<g>
          <line x1={wallRX} y1={parLTop} x2={wallRX} y2={yRoofR} stroke={CY} strokeWidth="1"/>
          {rows(parLTop,yRoofR).map((y,i)=><line key={i} x1={wallRX} y1={y} x2={wallRX+aLee} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArr2)"/>)}
        </g>}

        {/* WINDWARD / LEEWARD vertical labels beside each parapet */}
        {parW>0 && <text x={wallLX+9} y={wMid} fill="#6B7684" fontSize="6" letterSpacing=".12em" textAnchor="middle" transform={`rotate(-90,${wallLX+9},${wMid})`}>WINDWARD</text>}
        {parL>0 && <text x={wallRX-9} y={lMid} fill="#6B7684" fontSize="6" letterSpacing=".12em" textAnchor="middle" transform={`rotate(-90,${wallRX-9},${lMid})`}>LEEWARD</text>}

        {/* story + floor labels */}
        <text x={cx} y={lblY2+2} fill="#6B7684" fontSize="8" letterSpacing=".14em" textAnchor="middle">2ND STORY</text>
        <text x={cx} y={lblY1+2} fill="#6B7684" fontSize="8" letterSpacing=".14em" textAnchor="middle">1ST STORY</text>
        <text x={cx} y={wallBot+13} fill="#6B7684" fontSize="6.5" letterSpacing=".1em" textAnchor="middle">1ST FLOOR · FOUNDATION</text>

        {/* diaphragm load callouts (gold leaders to the right, anchored at the leeward points) */}
        <line x1={wallRX} y1={yRoofR} x2={calloutX-2} y2={yRoofR} stroke={GOLD} strokeWidth=".7" strokeDasharray="2 2"/>
        <text x={calloutX} y={yRoofR-2.5} fill={GOLD} fontSize="7" fontWeight="700">Level 2 diaphragm</text>
        <text x={calloutX} y={yRoofR+7}  fill={GOLD} fontSize="9" fontWeight="700">{fmt1(roofLL)} plf</text>
        <line x1={wallRX} y1={yF2R} x2={calloutX-2} y2={yF2R} stroke={GOLD} strokeWidth=".7" strokeDasharray="2 2"/>
        <text x={calloutX} y={yF2R-2.5} fill={GOLD} fontSize="7" fontWeight="700">Level 1 diaphragm</text>
        <text x={calloutX} y={yF2R+7}  fill={GOLD} fontSize="9" fontWeight="700">{fmt1(floorLL)} plf</text>

        {/* pressure boxes (blue) */}
        <Box cx={wallLX-aWall/2} cy={(yRoofL+wallBot)/2} text={`${fmt1(pw)} psf`} color={C_DIMBOX} field="pw" prop="pw" rot={-90}/>
        {parW>0&&<Box cx={wallLX-aWind/2} cy={wMid} text={`${fmt1(qW)} psf`} color={C_DIMBOX} field="wQ" prop="qWind" rot={-90}/>}
        {parL>0&&<Box cx={wallRX+aLee/2} cy={lMid} text={`${fmt1(qL)} psf`} color={C_DIMBOX} field="lQ" prop="qLee" rot={-90}/>}
        {/* height boxes (red) — windward H₂/H (left), leeward H₂/H (right), parapets */}
        <Box cx={wallLX+20} cy={mid2L} text={`${fmt1(H2)} ft`}  color={C_REACTBOX} field="H2"    prop="H2"/>
        <Box cx={wallLX+20} cy={mid1L} text={`${fmt1(H1)} ft`}  color={C_REACTBOX} field="H"     prop="H"/>
        <Box cx={wallRX-20} cy={mid2R} text={`${fmt1(LH2)} ft`} color={C_REACTBOX} field="leeH2" prop="leeH2"/>
        <Box cx={wallRX-20} cy={mid1R} text={`${fmt1(LH1)} ft`} color={C_REACTBOX} field="leeH"  prop="leeH"/>
        {parW>0&&<Box cx={wallLX+22} cy={wMid} text={`${fmt1(parW)} ft`} color={C_REACTBOX} field="wH" prop="parW"/>}
        {parL>0&&<Box cx={wallRX-22} cy={lMid} text={`${fmt1(parL)} ft`} color={C_REACTBOX} field="lH" prop="parL"/>}
      </svg>

      {edit && (
        <input autoFocus type="number" inputMode="decimal" value={v[edit.field] ?? ""}
          onChange={upd(edit.field, edit.prop)} onBlur={()=>setEdit(null)}
          onKeyDown={e=>{ if(e.key==="Enter"||e.key==="Escape") setEdit(null); }}
          style={{ position:"absolute", left:`${edit.l}%`, top:`${edit.t}%`, transform:"translate(-50%,-50%)",
                   width:58, padding:"4px 6px", textAlign:"center",
                   background:"#FFFFFF", color:"#9A6B1F", border:"1.5px solid #9A6B1F", borderRadius:3, font:"700 13px ui-monospace,Menlo,monospace", outline:"none", zIndex:6 }}/>
      )}
    </div>
  );
}

/* ── CAD palette ── */
const C_BG="#FFFFFF", C_GRID="#E9E7DE", C_WALL="#1C2733", C_NODE="#23577F",
      C_LOAD="#23577F", C_REACT="#B23A2A", C_DIMBOX="#23577F", C_REACTBOX="#B23A2A", C_DRAFT="#9A6B1F";
const C_ONESTORY="#2E6B4F";   // (2-story mode) wall tagged as 1-story only — drawn green to stand out

// (rev 39) nearest 2-story wall standing DOWNWIND of a windward wall (one face), so a 1-story cut can
// draw the stepped section + the ½·H₂·pw it pours forward. Mirrors buildSecDataF1's `backs` scan.
function nearestTwoStoryBehind(key, axis, sign, graph, propsFor, isOne){
  const e0=graph.edges.find(x=>keyOf(x)===key); if(!e0) return null;
  const a0=graph.nodes.find(n=>n.id===e0.a), b0=graph.nodes.find(n=>n.id===e0.b); if(!a0||!b0) return null;
  const travel = axis==="v" ? {x:0,y:sign} : {x:sign,y:0};
  const along=(p)=> p.x*travel.x + p.y*travel.y;
  const sOf =(p)=> axis==="v" ? p.x : p.y;
  const recv = axis==="v" ? "h" : "v";
  const depth=(along(a0)+along(b0))/2;
  const ws0=Math.min(sOf(a0),sOf(b0)), ws1=Math.max(sOf(a0),sOf(b0));
  let best=null, bestD=Infinity;
  for(const e of graph.edges){
    if(keyOf(e)===key) continue;
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b); if(!a||!b) continue;
    if(edgeAxis(a,b)!==recv) continue;
    if(isOne(keyOf(e))) continue;                                  // only 2-story walls
    const d=(along(a)+along(b))/2; if(d<=depth+0.6) continue;       // downwind only
    const lo=Math.max(ws0,Math.min(sOf(a),sOf(b))), hi=Math.min(ws1,Math.max(sOf(a),sOf(b)));
    if(hi-lo>0.5 && d<bestD){ bestD=d; best=keyOf(e); }
  }
  return best ? propsFor(best) : null;
}

// (rev 40) The ORDERED run of across-wind walls an overall-building section cut crosses at across-wind
// position `sAcross`, front (windward) → back (leeward) by downwind depth. Floor-INDEPENDENT (always
// the full graph). Drives both the section TYPE (from the 1/2-story pattern: 1·2·2·1=A, 1·1=B,
// 1·2·2=C, 2·2·1=C-rev) and the SecDiagramSeq drawing. Each entry carries the wall's own props.
function sectionSequence(sAcross, axis, sign, graph, propsFor, isOne){
  if(sAcross==null || sign==null) return [];
  const travel = axis==="v" ? {x:0,y:sign} : {x:sign,y:0};
  const along=(p)=> p.x*travel.x + p.y*travel.y;
  const sOf =(p)=> axis==="v" ? p.x : p.y;
  const recv = axis==="v" ? "h" : "v";
  const hits=[];
  for(const e of graph.edges){
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b); if(!a||!b) continue;
    if(edgeAxis(a,b)!==recv) continue;
    const s0=Math.min(sOf(a),sOf(b)), s1=Math.max(sOf(a),sOf(b));
    if(sAcross < s0-0.6 || sAcross > s1+0.6) continue;     // the cut line crosses this wall
    const p=propsFor(keyOf(e));
    hits.push({ key:keyOf(e), depth:(along(a)+along(b))/2, one:!!isOne(keyOf(e)),
                H:p.H, H2:p.H2, par:p.par, pw:p.pw, qWind:p.qWind, qLee:p.qLee });
  }
  hits.sort((a,b)=>a.depth-b.depth);                        // windward (front) → leeward (back)
  return hits;
}

/* (rev 39) STEPPED MIXED-height section — a 1-story windward wall WITH a 2-story portion behind it
   (the user's "1ST FLOOR PLAN" SECTION A). Short green windward wall + parapet in front, the taller
   2-story block behind rising to the roof, the leeward wall, the floor diaphragm at the 1-story level
   and the roof diaphragm over the block. The floor-diaphragm line load picks up ½·H₂·pw from the block
   → the 454. The block height is display-only (it comes from the 2-story wall on the plan); the
   windward wall's own fields stay editable. SecDiagram / SecDiagram2 are untouched. */
/* (rev 40) GENERAL OVERALL-BUILDING SECTION — draws whatever ordered run of walls the cut crosses,
   front (windward) → back (leeward), each at its own story height. This single renderer covers all
   of the schematic's section types from the wall SEQUENCE alone:
     1→2→2→1  = Section A   ·   1→1 = Section B (handled by SecDiagram)   ·   1→2→2 = Section C
     2→2→1    = Section C reverse.
   `seq` = [{one,H,H2,par,pw,qWind,qLee}, …] front→back (one = tagged 1-story). The floor diaphragm
   runs across every wall at the 1-story top; the roof diaphragm spans the contiguous 2-story block.
   The front & back walls are editable through the live `v`/`upd` buffer; interior walls are display
   only (their props come from the plan). SecDiagram / SecDiagram2 are untouched. */
function SecDiagramSeq({ seq, v, upd, floorLL, roofLL, commit }){
  const [edit,setEdit]=useState(null);
  const [ebuf,setEbuf]=useState({});          // (rev 42) raw-string buffer for INTERIOR-wall inputs (key-based), so "13." survives typing
  const num=s=>Math.max(0,parseFloat(s)||0);
  const N=Math.max(seq.length,1), last=N-1;
  const propOf=(i)=>{ const w=seq[i]||{};
    if(i===0)    return { one:w.one, H:num(v.H),    H2:num(v.H2 ?? w.H2), par:num(v.wH), pw:num(v.pw),  q:num(v.wQ) };
    if(i===last) return { one:w.one, H:num(v.leeH), H2:num(v.leeH2 ?? w.H2), par:num(v.lH), pw:num(w.pw), q:num(v.lQ) };
    return { one:w.one, H:num(w.H), H2:num(w.H2), par:num(w.par), pw:num(w.pw), q:num(w.qWind) };
  };
  const W=seq.map((_,i)=>propOf(i));
  const H1=Math.max(1,...W.map(w=>w.H));
  const H2box=Math.max(0,...W.filter(w=>!w.one).map(w=>w.H2));
  const VBW=380, VBH=300, padTop=22, padBot=30, availH=VBH-padTop-padBot, wallBot=padTop+availH;  // (rev 41) wider → room for the right-side callouts
  const maxFt=Math.max(1,...W.map(w=>(w.one?w.H:w.H+w.H2)+w.par));
  const pxPerFt=availH/maxFt;
  const leftX=70, rightX=250, sp=rightX-leftX;   // (rev 41) walls pulled left so the diaphragm callouts no longer overlap the leeward wall line
  const xAt=(i)=> N<=1?leftX:(leftX + i*sp/(N-1));
  const topY=(w)=> wallBot - (w.one? w.H : w.H+w.H2)*pxPerFt;
  // (rev 43) PER-WALL diaphragm levels so the diaphragm lines CONNECT to each wall's own top and the
  // section DEFORMS as a connected shape when a height changes (the 1-story's sloping ROOF LINE,
  // generalized to N walls), instead of a flat line pinned at the max height. floorY = a wall's
  // 1st-story top (Level-1/floor node); roofY = a 2-story wall's full top (Level-2/roof node). When the
  // heights all match these collapse to the old flat lines, so a uniform building looks unchanged.
  const floorY=(i)=> wallBot - W[i].H*pxPerFt;
  const roofY =(i)=> wallBot - (W[i].H + (W[i].one?0:W[i].H2))*pxPerFt;
  const yF2 = wallBot - H1*pxPerFt;                 // max 1-story top (kept for scale/label fallback)
  const yRoof= wallBot - (H1+H2box)*pxPerFt;        // max block top
  const CY="#23577F", YEL="#1C2733", GOLD="#9A6B1F", GRN="#2E6B4F", GRY="#6B7684";
  const pw0=W[0].pw, q0=W[0].q, qL=W[last].q;
  // (rev 41) scale the arrows over EVERY wall's pressures (incl. the 2-story block), so the block's
  // windward/parapet/leeward arrows are proportional and fit the 30px budget.
  const maxPsf=Math.max(pw0,q0,qL,1,...seq.map(w=>Math.max(num(w.pw),num(w.qWind),num(w.qLee)))), aS=30/maxPsf;
  const aOf=(psf)=> psf>0?Math.max(psf*aS,6):0;
  const aWall=aOf(pw0), aWind=aOf(q0), aLee=aOf(qL);
  const rows=(yTop,yBot)=>{ const n=Math.max(1,Math.round((yBot-yTop)/8)); return Array.from({length:n+1},(_,i)=>yTop+(yBot-yTop)*i/n); };
  // (rev 42) `open` carries an optional edge `key`: when set, the floating input edits THAT wall's props
  // directly via `commit(key,prop,val)` (interior block walls); when absent it uses the v/upd front-back path.
  const open=(field,prop,cx,cy,key)=>setEdit({field,prop,key,l:cx/VBW*100,t:cy/VBH*100});
  const seqVal=(key,prop)=>{ const w=seq.find(s=>s.key===key)||{}; return num(w[prop]); };   // current value for a keyed input
  const Box=({cx,cy,text,color,field,prop,rot=0,ed=true,wkey})=>{ const w=text.length*4.1+6,h=11;
    return (<g style={{cursor:ed?"pointer":"default"}} onClick={ed?()=>open(field,prop,cx,cy,wkey):undefined} transform={rot?`rotate(${rot},${cx},${cy})`:undefined}>
      <rect x={cx-w/2} y={cy-h/2} width={w} height={h} rx={1.5} fill={color}/>
      <text x={cx} y={cy+0.4} fill="#fff" fontSize={7} fontWeight={700} textAnchor="middle" dominantBaseline="middle" style={{userSelect:"none"}}>{text}</text></g>); };
  const twoIdx=W.map((w,i)=>w.one?-1:i).filter(i=>i>=0);   // indices of 2-story walls (the block)
  const calloutX=300;   // (rev 41) right of rightX(250)+leeward arrows → no overlap with the wall line
  const cFloorY=floorY(last);                                   // (rev 43) anchor the Level-1 callout to the floor diaphragm's leeward END
  const cRoofY = twoIdx.length ? roofY(twoIdx[twoIdx.length-1]) : yRoof;   // Level-2 callout → roof diaphragm's leeward end
  return (
   <div style={{position:"relative"}}>
    <svg viewBox={`0 0 ${VBW} ${VBH}`} style={{width:"100%",height:"auto",display:"block"}}>
      <defs><marker id="dArrM" markerWidth="6" markerHeight="6" refX="4.6" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6 Z" fill={CY}/></marker></defs>
      <rect x="0" y="0" width={VBW} height={VBH} fill={C_BG} rx="6"/>
      {/* foundation */}
      <line x1={xAt(0)} y1={wallBot} x2={xAt(last)} y2={wallBot} stroke={YEL} strokeWidth="1.4"/>
      {/* (rev 43) LEVEL-1 (floor) diaphragm — a POLYLINE through every wall's own 1st-story top with a NODE
          at each, so changing any wall's H makes the diaphragm slope/step and the section deforms as one
          connected shape (like the 1-story sloping ROOF LINE). Flat when all 1st-story heights match. */}
      <polyline points={W.map((w,i)=>`${xAt(i)},${floorY(i)}`).join(" ")} fill="none" stroke={GOLD} strokeWidth="1.3" strokeDasharray="5 3"/>
      {W.map((w,i)=><circle key={"fn"+i} cx={xAt(i)} cy={floorY(i)} r="2" fill={GOLD} stroke="#fff" strokeWidth="1"/>)}
      {/* (rev 43) LEVEL-2 (roof) diaphragm — polyline through the 2-story block walls' full tops + nodes */}
      {twoIdx.length>0 && <polyline points={twoIdx.map(i=>`${xAt(i)},${roofY(i)}`).join(" ")} fill="none" stroke={YEL} strokeWidth="1.4"/>}
      {twoIdx.map(i=><circle key={"rn"+i} cx={xAt(i)} cy={roofY(i)} r="2" fill={YEL} stroke="#fff" strokeWidth="1"/>)}
      {/* each wall in the cut, front → back (its top coincides with its diaphragm node, so they connect) */}
      {W.map((w,i)=>{ const x=xAt(i), ty=topY(w), pty=ty-w.par*pxPerFt, col=w.one?GRN:YEL;
        return (<g key={i}>
          <line x1={x} y1={ty} x2={x} y2={wallBot} stroke={col} strokeWidth={w.one?1.8:1.6}/>
          {w.par>0 && <line x1={x} y1={ty} x2={x} y2={pty} stroke={col} strokeWidth={w.one?1.8:1.6}/>}
          {w.par>0 && <circle cx={x} cy={pty} r="1.7" fill={col} stroke="#fff" strokeWidth=".8"/>}
          <text x={x} y={wallBot+11} fill={w.one?GRN:GRY} fontSize="5.6" fontWeight="700" textAnchor="middle">{w.one?"1-STY":"2-STY"}</text>
        </g>); })}
      {/* windward pressure (front wall: full height + parapet) */}
      {(()=>{ const x=xAt(0), w=W[0], ty=topY(w), pty=ty-w.par*pxPerFt; return (<g>
        {w.pw>0&&<g><line x1={x-aWall} y1={ty} x2={x-aWall} y2={wallBot} stroke={CY} strokeWidth="1"/>
          {rows(ty,wallBot).map((y,k)=><line key={k} x1={x-aWall} y1={y} x2={x} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g>}
        {w.par>0&&w.q>0&&<g><line x1={x-aWind} y1={pty} x2={x-aWind} y2={ty} stroke={CY} strokeWidth="1"/>
          {rows(pty,ty).map((y,k)=><line key={k} x1={x-aWind} y1={y} x2={x} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g>}
      </g>); })()}
      {/* leeward parapet pressure (back wall) */}
      {(()=>{ const x=xAt(last), w=W[last], ty=topY(w), pty=ty-w.par*pxPerFt; return (w.par>0&&w.q>0?
        <g><line x1={x} y1={pty} x2={x} y2={ty} stroke={CY} strokeWidth="1"/>
          {rows(pty,ty).map((y,k)=><line key={k} x1={x} y1={y} x2={x+aLee} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g> : null); })()}
      {/* (rev 41) 2-STORY BLOCK pressures — the windward upper-story + parapet (and the leeward parapet)
          that feed the LEVEL-2 (roof) diaphragm. These were missing: the block walls drew as bare lines.
          Windward face = the front-most 2-story wall (only its UPPER story + parapet see wind; the lower
          story is shadowed by whatever is in front of it). Leeward face = the back-most 2-story wall
          (parapet). When a block end coincides with the sequence front/back it is already drawn above. */}
      {twoIdx.length>0 && (()=>{
        const bw=twoIdx[0], bl=twoIdx[twoIdx.length-1];
        const fw=W[bw], fx=xAt(bw), fTop=topY(fw), fFloor=wallBot-fw.H*pxPerFt, fpTop=fTop-fw.par*pxPerFt;
        const fQ=num((seq[bw]||{}).qWind), aFp=aOf(fQ);          // block-front windward parapet pressure
        const bwl=W[bl], bx=xAt(bl), bTop=topY(bwl), bpTop=bTop-bwl.par*pxPerFt;
        const bQ=num((seq[bl]||{}).qLee), aBp=aOf(bQ);           // block-back leeward parapet pressure
        return (<g>
          {bw!==0 && fw.pw>0 && <g>{/* windward UPPER story (roof→floor of the block) — lower story shadowed */}
            <line x1={fx-aWall} y1={fTop} x2={fx-aWall} y2={fFloor} stroke={CY} strokeWidth="1"/>
            {rows(fTop,fFloor).map((y,k)=><line key={"bfu"+k} x1={fx-aWall} y1={y} x2={fx} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g>}
          {bw!==0 && fw.par>0 && fQ>0 && <g>{/* windward parapet */}
            <line x1={fx-aFp} y1={fpTop} x2={fx-aFp} y2={fTop} stroke={CY} strokeWidth="1"/>
            {rows(fpTop,fTop).map((y,k)=><line key={"bfp"+k} x1={fx-aFp} y1={y} x2={fx} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g>}
          {bl!==last && bwl.par>0 && bQ>0 && <g>{/* leeward parapet (arrows to the right) */}
            <line x1={bx} y1={bpTop} x2={bx} y2={bTop} stroke={CY} strokeWidth="1"/>
            {rows(bpTop,bTop).map((y,k)=><line key={"bbp"+k} x1={bx} y1={y} x2={bx+aBp} y2={y} stroke={CY} strokeWidth=".7" markerEnd="url(#dArrM)"/>)}</g>}
        </g>);
      })()}
      {/* labels + diaphragm callouts */}
      <text x={(xAt(0)+xAt(last))/2} y={wallBot+22} fill={GRY} fontSize="6.5" letterSpacing=".1em" textAnchor="middle">1ST FLOOR · FOUNDATION</text>
      {twoIdx.length>0 && <g>
        <line x1={xAt(twoIdx[twoIdx.length-1])} y1={cRoofY} x2={calloutX-2} y2={cRoofY} stroke={GOLD} strokeWidth=".7" strokeDasharray="2 2"/>
        <text x={calloutX} y={cRoofY-2.5} fill={GOLD} fontSize="6.8" fontWeight="700">Level 2 diaphragm</text>
        <text x={calloutX} y={cRoofY+7.5} fill={GOLD} fontSize="9.5" fontWeight="700">{fmt1(roofLL)} plf</text></g>}
      <line x1={xAt(last)} y1={cFloorY} x2={calloutX-2} y2={cFloorY} stroke={GOLD} strokeWidth=".7" strokeDasharray="2 2"/>
      <text x={calloutX} y={cFloorY-2.5} fill={GOLD} fontSize="6.8" fontWeight="700">Level 1 diaphragm</text>
      <text x={calloutX} y={cFloorY+7.5} fill={GOLD} fontSize="9.5" fontWeight="700">{fmt1(floorLL)} plf</text>
      {/* editable FRONT (windward) wall boxes */}
      {(()=>{ const x=xAt(0), w=W[0], ty=topY(w), pty=ty-w.par*pxPerFt, y2=wallBot-w.H*pxPerFt; return (<g>
        {w.pw>0&&<Box cx={x-aWall/2} cy={(ty+wallBot)/2} text={`${fmt1(w.pw)} psf`} color={C_DIMBOX} field="pw" prop="pw" rot={-90}/>}
        <Box cx={x+13} cy={(y2+wallBot)/2} text={`${fmt1(w.H)} ft`} color={C_REACTBOX} field="H" prop="H"/>
        {!w.one&&w.H2>0&&<Box cx={x+13} cy={(ty+y2)/2} text={`${fmt1(w.H2)} ft`} color={C_REACTBOX} field="H2" prop="H2"/>}
        {w.par>0&&<Box cx={x-aWind/2} cy={(pty+ty)/2} text={`${fmt1(w.q)} psf`} color={C_DIMBOX} field="wQ" prop="qWind" rot={-90}/>}
        {w.par>0&&<Box cx={x+13} cy={(pty+ty)/2} text={`${fmt1(w.par)} ft`} color={C_REACTBOX} field="wH" prop="parW"/>}
      </g>); })()}
      {/* (rev 44) editable BACK (leeward-most) wall — its HEIGHT (and H₂ if 2-story) is ALWAYS editable
          for correct geometry, even though this wall carries no diaphragm load (mirrors the 1-story's
          editable leeward HR, which tilts the roof line without contributing to the wall load). Its
          parapet height + leeward parapet pressure stay editable too. leeH/leeH2 route to the back wall. */}
      {(()=>{ const x=xAt(last), w=W[last], ty=topY(w), pty=ty-w.par*pxPerFt, y2=wallBot-w.H*pxPerFt; return (<g>
        <Box cx={x-13} cy={(y2+wallBot)/2} text={`${fmt1(w.H)} ft`} color={C_REACTBOX} field="leeH" prop="leeH"/>
        {!w.one && w.H2>0 && <Box cx={x-13} cy={(ty+y2)/2} text={`${fmt1(w.H2)} ft`} color={C_REACTBOX} field="leeH2" prop="leeH2"/>}
        {w.par>0 && w.q>0 && <Box cx={x+aLee/2} cy={(pty+ty)/2} text={`${fmt1(w.q)} psf`} color={C_DIMBOX} field="lQ" prop="qLee" rot={-90}/>}
        {w.par>0 && <Box cx={x-13} cy={(pty+ty)/2} text={`${fmt1(w.par)} ft`} color={C_REACTBOX} field="lH" prop="parL"/>}
      </g>); })()}
      {/* (rev 42) editable INTERIOR 2-story BLOCK walls — height + pressure, written straight to each wall's
          own props by key (front block = windward face: pw·H·H₂·par·qWind; back block = leeward face:
          qLee·par·H·H₂). Only for block ends that are NOT the sequence front/back (those use the boxes above). */}
      {twoIdx.length>0 && (()=>{
        const bw=twoIdx[0], bl=twoIdx[twoIdx.length-1];
        const fr = bw!==0 && (()=>{ const x=xAt(bw), w=W[bw], k=(seq[bw]||{}).key, ty=topY(w), fFloor=wallBot-w.H*pxPerFt, pty=ty-w.par*pxPerFt, qW=num((seq[bw]||{}).qWind);
          return (<g>
            {w.pw>0 && <Box cx={x-aWall/2} cy={(ty+fFloor)/2} text={`${fmt1(w.pw)} psf`} color={C_DIMBOX} prop="pw" wkey={k} rot={-90}/>}
            <Box cx={x+13} cy={(fFloor+wallBot)/2} text={`${fmt1(w.H)} ft`} color={C_REACTBOX} prop="H" wkey={k}/>
            <Box cx={x+13} cy={(ty+fFloor)/2}     text={`${fmt1(w.H2)} ft`} color={C_REACTBOX} prop="H2" wkey={k}/>
            {w.par>0 && <Box cx={x+13}      cy={(pty+ty)/2} text={`${fmt1(w.par)} ft`} color={C_REACTBOX} prop="par" wkey={k}/>}
            {w.par>0 && <Box cx={x-aOf(qW)/2} cy={(pty+ty)/2} text={`${fmt1(qW)} psf`} color={C_DIMBOX} prop="qWind" wkey={k} rot={-90}/>}
          </g>); })();
        const bk = bl!==last && (()=>{ const x=xAt(bl), w=W[bl], k=(seq[bl]||{}).key, ty=topY(w), fFloor=wallBot-w.H*pxPerFt, pty=ty-w.par*pxPerFt, qLv=num((seq[bl]||{}).qLee);
          return (<g>
            {w.par>0 && qLv>0 && <Box cx={x+aOf(qLv)/2} cy={(pty+ty)/2} text={`${fmt1(qLv)} psf`} color={C_DIMBOX} prop="qLee" wkey={k} rot={-90}/>}
            {w.par>0 && <Box cx={x-13} cy={(pty+ty)/2} text={`${fmt1(w.par)} ft`} color={C_REACTBOX} prop="par" wkey={k}/>}
            <Box cx={x-13} cy={(fFloor+wallBot)/2} text={`${fmt1(w.H)} ft`} color={C_REACTBOX} prop="H" wkey={k}/>
            <Box cx={x-13} cy={(ty+fFloor)/2}     text={`${fmt1(w.H2)} ft`} color={C_REACTBOX} prop="H2" wkey={k}/>
          </g>); })();
        return (<g>{fr||null}{bk||null}</g>);
      })()}
    </svg>
    {edit && (
      <input autoFocus type="number" inputMode="decimal"
        value={ edit.key ? (ebuf[`${edit.key}:${edit.prop}`] ?? String(seqVal(edit.key,edit.prop))) : (v[edit.field] ?? "") }
        onChange={ edit.key
          ? (e)=>{ const raw=e.target.value; setEbuf(p=>({ ...p, [`${edit.key}:${edit.prop}`]:raw })); commit(edit.key, edit.prop, num(raw)); }
          : upd(edit.field, edit.prop) }
        onBlur={()=>{ if(edit&&edit.key){ const kk=`${edit.key}:${edit.prop}`; setEbuf(p=>{ const n={...p}; delete n[kk]; return n; }); } setEdit(null); }}
        onKeyDown={e=>{ if(e.key==="Enter"||e.key==="Escape") e.target.blur(); }}
        style={{ position:"absolute", left:`${edit.l}%`, top:`${edit.t}%`, transform:"translate(-50%,-50%)",
                 width:58, padding:"4px 6px", textAlign:"center",
                 background:"#FFFFFF", color:"#9A6B1F", border:"1.5px solid #9A6B1F", borderRadius:3, font:"700 13px ui-monospace,Menlo,monospace", outline:"none", zIndex:6 }}/>
    )}
   </div>
  );
}

/* masked label box (blue for dimensions, red for reactions) — readable over any line */
function Tag({ x, y, text, box, S, rot=0, ts=1 }) {
  const fs=1.35*S*ts, w=text.length*fs*0.64+0.9*S*ts, h=fs*1.35;
  return (
    <g transform={rot?`rotate(${rot},${x},${y})`:undefined}>
      <rect x={x-w/2} y={y-h/2} width={w} height={h} rx={0.3*S*ts} fill={box}/>
      <text x={x} y={y+0.15*S*ts} fill="#fff" fontSize={fs} fontWeight="700"
            textAnchor="middle" dominantBaseline="middle">{text}</text>
    </g>
  );
}

/* stable field — defined at module scope so it never remounts (keeps focus) */
function Field({ label, unit, value, onChange }) {
  return (
    <div className="fld">
      <label>{label}</label>
      <div style={{ position:"relative" }}>
        <input type="number" min="0" step="0.1" value={value ?? ""} onChange={onChange}
               style={{ width:"100%", paddingRight:36 }}/>
        <span style={{ position:"absolute", right:9, top:"50%", transform:"translateY(-50%)", fontSize:10, color:"#7e8db5" }}>{unit}</span>
      </div>
    </div>
  );
}

/* ═══════════════ WINDWARD LINE-LOAD (static, CAD style) ═══════════════ */
function WindLoad({ load, onOpen, S=1, ts=1, displayPlf=null, prec=1 }) {
  const { nx, ny } = load;
  // one group per leeward sub-region (split where the back wall's parapet changes). Adjacent
  // sub-regions that resolve to the SAME plf are merged into one span here so the wall shows a
  // single load label — two labels appear ONLY where the line load actually changes along the wall
  // (matching the dashed tributary divide, which is likewise drawn only where plf differs).
  const raw = (load.subLoads && load.subLoads.length)
    ? load.subLoads
    : [{ a:load.wa, b:load.wb, plf:load.total }];
  let segs = [];
  if(displayPlf!=null){
    // rev 34 — 2-story FLOOR-1 view: the floor diaphragm load (½·H·pw + ½·H₂·pw) is uniform along the
    // wall (the leeward-parapet term lives only in the ROOF diaphragm, which transfers down through the
    // shear walls, not the floor diaphragm), so collapse to ONE span showing the floor-only plf.
    segs = [{ a:load.wa, b:load.wb, plf:displayPlf }];
  } else {
    for(const sg of raw){
      const prev = segs[segs.length-1];
      if(prev && Math.abs(prev.plf - sg.plf) < 0.5) prev.b = sg.b;   // same plf → extend the span
      else segs.push({ a:sg.a, b:sg.b, plf:sg.plf });
    }
  }
  return (
    <g style={{cursor:"pointer"}} onPointerDown={e=>e.stopPropagation()} onClick={onOpen}>
      {segs.map((sg,si)=>{
        const wa=sg.a, wb=sg.b, total=sg.plf;
        const len=Math.hypot(wb.x-wa.x, wb.y-wa.y);
        const aLen = clamp(total/55, 3, 8) * 0.5 * S * ts;   // rev 32: scales with Markup (ts); base *0.5 (original)
        const n = Math.max(2, Math.round(len/(5.5*S)));
        const tip = 0.3*S*ts;                               // rev 32: scales with Markup; base 0.3 (original)
        const b1={x:wa.x+nx*aLen, y:wa.y+ny*aLen}, b2={x:wb.x+nx*aLen, y:wb.y+ny*aLen};
        const arrows=[];
        for(let i=0;i<=n;i++){
          const f=i/n, px=wa.x+(wb.x-wa.x)*f, py=wa.y+(wb.y-wa.y)*f;
          arrows.push({k:i, x1:px+nx*aLen, y1:py+ny*aLen, x2:px+nx*tip, y2:py+ny*tip});
        }
        const wallVert = Math.abs(wb.y-wa.y) > Math.abs(wb.x-wa.x);
        const mx=(wa.x+wb.x)/2, my=(wa.y+wb.y)/2;
        const lx=mx+nx*(aLen+2.2*S*ts), ly=my+ny*(aLen+2.2*S*ts);
        return (
          <g key={si}>
            <line x1={b1.x} y1={b1.y} x2={b2.x} y2={b2.y} stroke={C_LOAD} strokeWidth={0.2*S*ts}/>
            {arrows.map(a=>(
              <line key={a.k} x1={a.x1} y1={a.y1} x2={a.x2} y2={a.y2} stroke={C_LOAD} strokeWidth={0.16*S*ts} markerEnd="url(#loadArr)"/>
            ))}
            <text x={lx} y={ly} fill={C_LOAD} fontSize={1.35*S*ts} fontWeight="600" textAnchor="middle" dominantBaseline="central"
                  transform={wallVert?`rotate(-90,${lx},${ly})`:undefined}>{(prec===2?fmt2:fmt1)(total)} plf</text>
          </g>
        );
      })}
    </g>
  );
}

/* aggregated reaction on a (possibly shared) support — drawn as a compact "rocket": the bold
   arrowhead (nose) terminates AT the support node and the label box is the body, trailing to the
   windward side along the load direction (tdir). On vertical walls the load runs down the wall, so
   the label is rotated to lie ALONG the shaft — text + arrowhead read as one rocket (matching the
   horizontal case) instead of a horizontal chip with an arrow poking out of it. */
function Reaction({ r, tdir, S, ts=1 }) {
  const dx=tdir.x, dy=tdir.y;
  const vert = Math.abs(dy) > Math.abs(dx);               // vertical rocket → rotate label to lie along the shaft
  const shaft=2.1*S*ts;                                   // rev 32: scales with Markup (ts); base 2.1 (original)
  const hx=r.ax, hy=r.ay;                                  // nose tip at the support node
  const tx=r.ax-dx*shaft, ty=r.ay-dy*shaft;                // shaft tail (windward side)
  const lx=r.ax-dx*(shaft+1.55*S*ts), ly=r.ay-dy*(shaft+1.55*S*ts); // label body behind the shaft (gap scales too)
  return (
    <g>
      <line x1={tx} y1={ty} x2={hx} y2={hy} stroke={C_REACT} strokeWidth={0.42*S*ts} strokeLinecap="round" markerEnd="url(#reactArr)"/>
      <Tag x={lx} y={ly} text={`${fmt2(r.kips)}k`} box={C_REACTBOX} S={S} ts={ts} rot={vert ? -90 : 0}/>
    </g>
  );
}

/* ═══════════════ WIND INPUT WINDOW ═══════════════ */
function WindWindow({ section, setVals, onReverse, onClose, onRemove, twoStory, oneStory=false }) {
  // STEP 4: a wall tagged 1-story (in 2-story mode) reaches only the floor diaphragm, so its section
  // cut is a SINGLE-story elevation + a single total line load — not the 2-story roof/floor split.
  const twoStoryView = twoStory && !oneStory;
  const [v, setV] = useState({});
  // seed once per open (key carries section + leeward-partner identity) → decimals survive typing
  useEffect(() => {
    const s = section || {};
    setV({ H:String(s.H||0), pw:String(s.pw||0), leeH:String(s.leeH||0),  // leeH = leeward (back) wall height
           H2:String(s.H2||0), leeH2:String(s.leeH2||0),                  // 2nd-story heights (windward / leeward)
           wH:String(s.par||0),    wQ:String(s.qWind||0),   // windward parapet = THIS wall's own
           lH:String(s.leePar||0), lQ:String(s.qLee||0) }); // leeward parapet = BACK wall's own
  }, []); // eslint-disable-line
  const num = (s) => Math.max(0, parseFloat(s) || 0);
  const upd = (field, prop) => (e) => {
    const raw = e.target.value;
    setV((p) => ({ ...p, [field]: raw }));
    // route each value to the wall it physically belongs to:
    if(prop==="parL")      setVals("lee",  { par:num(raw) });   // leeward parapet ht → back wall
    else if(prop==="parW") setVals("self", { par:num(raw) });   // windward parapet ht → this wall
    else if(prop==="leeH") setVals("lee",  { H:num(raw) });     // leeward WALL ht → back wall (sloping roof)
    else if(prop==="leeH2")setVals("lee",  { H2:num(raw) });    // leeward 2nd-story ht → back wall (2-story)
    else                   setVals("self", { [prop]:num(raw) });// H, pw, qWind, qLee → this wall
  };
  const wallRes = 0.5 * num(v.H) * num(v.pw);
  const windPar = num(v.wH) * num(v.wQ);
  const leePar  = num(v.lH) * num(v.lQ);
  const total = wallRes + windPar + leePar;
  // ── two-story diaphragm line loads (Step 3) — derived here in the UI, outside the frozen engine ──
  // (rev 41) The UI now LABELS these "Level 2" (the upper/roof diaphragm — designs the level-2 walls) and
  // "Level 1" (the lower/floor a.k.a. 2nd-floor diaphragm — designs the level-1 walls). The variable
  // names keep the physical roof/floor terms; only the displayed labels changed (no value/engine change).
  // The 2nd-story wall (H₂) splits: upper ½ → Level 2 (roof) diaphragm, lower ½ → Level 1 (floor) diaphragm.
  const wallRes2 = 0.5 * num(v.H2) * num(v.pw);        // ½·H₂·pw
  const roofLL   = wallRes2 + windPar + leePar;        // LEVEL 2 diaphragm = ½·H₂·pw + parapets  → designs level-2 (upper) walls
  // Level 1 diaphragm carries ONLY the half-walls directly above and below it (½·H·pw + ½·H₂·pw).
  // The Level 2 (roof) diaphragm + parapets do NOT pour into the Level 1 diaphragm — that load transfers
  // DOWN through the level-2 shear wall into the level-1 shear wall as a POINT load (stacked overturning
  // / holdown, unchanged). So this is the floor-only line load, not roof+floor combined. (rev 34)
  const floorLL  = wallRes + wallRes2;                 // LEVEL 1 diaphragm = ½·H·pw + ½·H₂·pw  → designs level-1 (lower) walls
  // (rev 40) OVERALL-BUILDING section from the ordered wall sequence the cut crosses. The type falls
  // out of the 1/2-story pattern: 1·2·2·1 = A, 1·1 = B, 1·2·2 = C, 2·2·1 = C-reverse. Floor-independent.
  const seq = (section && section.seq) || [];
  const hasOne = seq.some(w=>w.one), hasTwo = seq.some(w=>!w.one);
  const mixedSeq = !!(twoStory && hasOne && hasTwo && seq.length>=2);
  // floor-diaphragm line load on the windward (front) wall — matches buildSecDataF1's baseOf:
  //   1-story front → ½·H·pw + own parapet + ½·H₂·pw of the nearest 2-story behind (one face)
  //   2-story front → ½·H·pw + ½·H₂·pw (its own)        … plus the leeward parapet if the BACK wall is 1-story.
  const w0 = seq[0]||{}, wL = seq[seq.length-1]||{};
  const seqAcc = w0.one ? (()=>{ const box=seq.find((w,i)=>i>0&&!w.one); return box?0.5*num(box.H2)*num(box.pw):0; })()
                        : 0.5*num(v.H2)*num(v.pw);
  const seqBase = 0.5*num(v.H)*num(v.pw) + (w0.one ? windPar : 0);
  const seqLeePar = (wL && wL.one) ? num(v.lH)*num(v.lQ) : 0;
  const floorLLmix = seqBase + seqLeePar + seqAcc;          // e.g. 478  (Level 1 diaphragm)
  // (rev 41) LEVEL 2 (roof) diaphragm of the 2-story BLOCK — same shape as the uniform roofLL above,
  // but read from the block's front/back walls (the schematic SECTION A's middle stack): ½·H₂·pw of the
  // block + the block's windward parapet + its leeward parapet. The block's end walls usually come from
  // the plan (interior, display-only); where a block end coincides with the editable sequence front/back
  // (Section C / C-reverse) the live `v` value is used so edits flow through.
  const twoIxSeq = seq.map((w,i)=>w.one?-1:i).filter(i=>i>=0);
  const bfI = twoIxSeq[0], bbI = twoIxSeq[twoIxSeq.length-1];
  const bf = (bfI!=null) ? seq[bfI] : null, bb = (bbI!=null) ? seq[bbI] : null;
  const blkH2  = bfI===0 ? num(v.H2) : num((bf||{}).H2);
  const blkPw  = bfI===0 ? num(v.pw) : num((bf||{}).pw);
  const blkWPar= bfI===0 ? num(v.wH)*num(v.wQ) : num((bf||{}).par)*num((bf||{}).qWind);
  const blkLPar= bbI===(seq.length-1) ? num(v.lH)*num(v.lQ) : num((bb||{}).par)*num((bb||{}).qLee);
  const roofLLseq = bf ? (0.5*blkH2*blkPw + blkWPar + blkLPar) : 0;   // Level 2 diaphragm (block)
  const reverse = () => { onReverse(); };
  return (
    <div className="ovl" onPointerDown={(e)=>{ if(e.target.classList.contains("ovl")) onClose(); }}>
      <div className="win">
        <div className="win-h">
          <div className="win-t">Wind Line Load — {section&&section.axis==="v"?"N–S":"E–W"}</div>
          <button className="win-x" onClick={onClose} title="Close">×</button>
        </div>
        <div className="win-b">
          <div style={{ marginBottom:12 }}>{
            mixedSeq ? <SecDiagramSeq seq={seq} v={v} upd={upd} floorLL={floorLLmix} roofLL={roofLLseq} commit={(key,prop,val)=>setVals(key,{[prop]:val})}/>
            : twoStoryView ? <SecDiagram2 v={v} upd={upd} roofLL={roofLL} floorLL={floorLL}/>
            : <SecDiagram v={v} upd={upd} />
          }</div>

          <button className="rev" onClick={reverse} style={{ marginBottom:12 }}>
            ⇄ Reverse wind direction
          </button>

          {mixedSeq ? (
            <div className="tot">
              <div className="lbl">Level 1 diaphragm line load <small>→ designs this {w0.one?"1-story":"2-story"} wall</small></div>
              <div className="v">{fmt1(floorLLmix)} <small>plf</small></div>
              <div style={{ marginTop:8, paddingTop:8, borderTop:"1px solid rgba(255,255,255,.08)" }}>
                <div className="brk"><span>½·H·pw — front wall</span><b>{fmt1(0.5*num(v.H)*num(v.pw))} plf</b></div>
                <div className="brk"><span>windward + leeward parapet</span><b>{fmt1((w0.one?windPar:0)+seqLeePar)} plf</b></div>
                {seqAcc>0 && <div className="brk"><span>½·H₂·pw — 2-story block {w0.one?"behind (poured fwd)":"(own upper wall)"}</span><b>{fmt1(seqAcc)} plf</b></div>}
              </div>
              {roofLLseq>0 && <>
                <div className="lbl" style={{ marginTop:14 }}>Level 2 diaphragm line load <small>→ designs the level-2 (2-story block) walls</small></div>
                <div className="v">{fmt1(roofLLseq)} <small>plf</small></div>
                <div style={{ marginTop:8, paddingTop:8, borderTop:"1px solid rgba(255,255,255,.08)" }}>
                  <div className="brk"><span>½·H₂·pw — 2-story block (upper ½)</span><b>{fmt1(0.5*blkH2*blkPw)} plf</b></div>
                  <div className="brk"><span>windward + leeward parapet (block)</span><b>{fmt1(blkWPar+blkLPar)} plf</b></div>
                </div>
              </>}
            </div>
          ) : twoStoryView ? (
            <div className="tot">
              <div className="lbl">Level 2 diaphragm line load <small>→ designs the level-2 (upper) shear walls</small></div>
              <div className="v">{fmt1(roofLL)} <small>plf</small></div>
              <div style={{ marginTop:8, paddingTop:8, borderTop:"1px solid rgba(255,255,255,.08)" }}>
                <div className="brk"><span>½·H₂·pw — 2nd-story wall (upper ½)</span><b>{fmt1(wallRes2)} plf</b></div>
                <div className="brk"><span>windward + leeward parapet</span><b>{fmt1(windPar+leePar)} plf</b></div>
              </div>
              <div className="lbl" style={{ marginTop:14 }}>Level 1 diaphragm line load <small>→ designs the level-1 (lower) shear walls</small></div>
              <div className="v">{fmt1(floorLL)} <small>plf</small></div>
              <div style={{ marginTop:8, paddingTop:8, borderTop:"1px solid rgba(255,255,255,.08)" }}>
                <div className="brk"><span>½·H₂·pw — 2nd-story wall (lower ½)</span><b>{fmt1(wallRes2)} plf</b></div>
                <div className="brk"><span>½·H·pw — 1st-story wall (upper ½)</span><b>{fmt1(wallRes)} plf</b></div>
              </div>
            </div>
          ) : (
            <div className="tot">
              <div className="lbl">Total wall line load</div>
              <div className="v">{fmt1(total)} <small>plf</small></div>
              <div style={{ marginTop:10, borderTop:"1px solid rgba(255,255,255,.08)", paddingTop:8 }}>
                <div className="brk"><span>Wall (H/2·pw)</span><b>{fmt1(wallRes)} plf</b></div>
                <div className="brk"><span>Windward parapet (hₗ·qₗ)</span><b>{fmt1(windPar)} plf</b></div>
                <div className="brk"><span>Leeward parapet (hᵣ·qᵣ)</span><b>{fmt1(leePar)} plf</b></div>
              </div>
            </div>
          )}

          <button className="btn pink" onClick={onRemove} style={{ marginTop:12, width:"100%" }}>
            Remove section cut
          </button>
        </div>
      </div>
    </div>
  );
}

// ── DL TRIBUTARY WINDOW (rev 49) ─────────────────────────────────────────────
// A small plan-side modal for entering a wall's DEAD-LOAD tributary widths (the
// values that feed the gravity self-weight resisting uplift). Opened from the wall
// right-click menu. In 2-story mode it carries an in-window Level 1 / Level 2 switch
// so the user can enter DIFFERENT trib for the 1st- and 2nd-floor walls of the same
// (stacked) wall without leaving the window; the header always names the level. The
// values are written straight onto wallProps[key] via setVals(key, patch) (rev-42
// explicit-key path), so they persist in the .wps session and flow to the Design tab
// (per line, per floor) and on to the Calculation sheet.
function DLTributaryWindow({ wprops, twoStory, activeFloor, oneStory, onSet, onClose }) {
  // (rev 50) oneStory = this wall is tagged 1-story inside 2-Story mode → it reaches the floor diaphragm
  // but never the roof, so it has NO 2nd-floor wall. The Level 2 control is greyed/disabled and the
  // level is pinned to 1 so no 2nd-floor trib can be entered for it.
  const [lvl, setLvl] = React.useState(!oneStory && twoStory && activeFloor === 2 ? 2 : 1);
  const isF2  = twoStory && !oneStory && lvl === 2;
  const rKey  = isF2 ? "roofTrib2"  : "roofTrib";
  const fKey  = isF2 ? "floorTrib2" : "floorTrib";
  const num   = (s) => Math.max(0, parseFloat(s) || 0);
  // string buffers so a partial decimal (e.g. "2.") survives typing; re-seed on level switch
  const [buf, setBuf] = React.useState({});
  React.useEffect(() => {
    setBuf({ f: String(wprops[fKey] ?? 0), r: String(wprops[rKey] ?? 0) });
  }, [lvl]); // eslint-disable-line react-hooks/exhaustive-deps
  const write = (which, raw) => {
    setBuf((b) => ({ ...b, [which]: raw }));
    onSet({ [which === "f" ? fKey : rKey]: num(raw) });
  };
  const lvlLabel = !twoStory ? "single-story wall"
                 : oneStory  ? "Level 1 · 1-story wall"
                 : (lvl === 2 ? "Level 2 · 2nd-floor wall" : "Level 1 · 1st-floor wall");
  const inputS = { width:96, padding:"6px 8px", border:"1px solid var(--line)", borderRadius:4,
                   fontSize:13, textAlign:"right", color:"var(--ink)" };
  return (
    <div className="ovl" onPointerDown={(e)=>{ if(e.target.classList.contains("ovl")) onClose(); }}>
      <div className="win" style={{ width:"min(380px,97vw)" }}>
        <div className="win-h">
          <div className="win-t">DL Tributary — {lvlLabel}</div>
          <button className="win-x" onClick={onClose} title="Close">×</button>
        </div>
        <div className="win-b">
          {twoStory && (
            <div style={{ display:"flex", gap:6, marginBottom: oneStory ? 6 : 12 }}>
              {[1,2].map((L)=>{
                const dis = oneStory && L === 2;        // a 1-story wall has no 2nd floor
                const on  = lvl === L;
                return (
                  <button key={L} disabled={dis} onClick={()=>{ if(!dis) setLvl(L); }}
                    title={dis ? "This wall is tagged 1-story — it has no 2nd floor" : undefined}
                    style={{ flex:1, padding:"7px 0", borderRadius:0, fontWeight:700, fontSize:12,
                             cursor: dis ? "not-allowed" : "pointer", opacity: dis ? 0.65 : 1,
                             border:`1.5px solid ${on && !dis ? "var(--accent)" : "var(--line)"}`,
                             background: dis ? "var(--bg)" : (on ? "var(--accent)" : "#FFFFFF"),
                             color: dis ? "var(--muted)" : (on ? "#FFFFFF" : "var(--ink)") }}>
                    {L === 1 ? "1st floor" : "2nd floor"}
                  </button>
                );
              })}
            </div>
          )}
          {twoStory && oneStory && (
            <div style={{ fontSize:11, color:"var(--hot)", marginBottom:12, lineHeight:1.4 }}>
              This wall is tagged <b>1-story</b> — Level 2 is greyed out (it has no 2nd floor).
            </div>
          )}
          <div style={{ fontSize:11, color:"var(--muted)", marginBottom:12, lineHeight:1.4 }}>
            Dead-load tributary widths for this wall{twoStory && !oneStory ? ` on the ${lvl === 2 ? "2nd" : "1st"} floor` : ""}.
            They combine with the global Roof / Floor DL (psf) to set the wall self-weight that resists
            uplift. These feed the Design tab and are sent to the Calculation sheet.
          </div>
          {[["f","Floor tributary"],["r","Roof tributary"]].map(([w,label])=>(
            <div key={w} style={{ display:"flex", alignItems:"center", justifyContent:"space-between", gap:10, marginBottom:10 }}>
              <label style={{ fontSize:13, fontWeight:600, color:"var(--ink)" }}>{label}</label>
              <div style={{ display:"flex", alignItems:"center", gap:6 }}>
                <input type="number" step={0.5} min={0} value={buf[w] ?? ""}
                       onChange={(e)=>write(w, e.target.value)} style={inputS}/>
                <span style={{ fontSize:12, color:"var(--muted)" }}>ft</span>
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}

// (rev 56) GLOBAL INPUTS — define wall/parapet height + wind pressures once and apply them to EVERY
// wall in the model, so a building with uniform walls doesn't need a section cut per wall. Opened from
// a side-panel button. The fields map onto the existing per-wall props (no new data-model field):
//   1-Story:  Wall Height→H · Parapet Height→par · Wall Pressure→pw · Windward/Leeward parapet→qWind/qLee
//   2-Story:  1st/2nd Wall Height→H/H2 · Wall/Windward/Leeward pressures→pw/qWind/qLee · and the two
//             parapet heights route by level — 1st-Level→par on walls tagged 1-story, 2nd-Level→par on
//             the full-height (2-story) walls (each physical wall still has exactly ONE `par`). Apply
//             writes wallProps for all edges; everything downstream (loads, reactions, section cuts,
//             design handoff) is already reactive to wallProps, so no engine touch. Seed values are the
//             building-wide consensus per field (uniform → that value; mixed → the default).
function GlobalInputsWindow({ seed, twoStory, hasOneStory, onApply, onClose }) {
  const [buf, setBuf] = React.useState(()=>{
    const s = {}; for(const k of Object.keys(seed)) s[k] = String(seed[k]); return s;
  });
  const write = (w, raw)=> setBuf(b=>({ ...b, [w]: raw }));
  const inputS = { width:96, padding:"6px 8px", border:"1px solid var(--line)", borderRadius:4,
                   fontSize:13, textAlign:"right", color:"var(--ink)" };
  const subH   = { fontSize:11, fontWeight:800, letterSpacing:".04em", textTransform:"uppercase",
                   color:"var(--muted)", margin:"2px 0 9px" };
  // [key, label, unit, step, hint]
  const heightFields = twoStory
    ? [["H",   "1st Level Wall Height",    "ft", 0.5, null],
       ["H2",  "2nd Level Wall Height",    "ft", 0.5, null],
       ["par1","1st Level Parapet Height", "ft", 0.5, hasOneStory ? "Applied to walls tagged 1-story" : "Applied to walls tagged 1-story (none yet)"],
       ["par2","2nd Level Parapet Height", "ft", 0.5, "Applied to the full-height 2-story walls"]]
    : [["H",   "Wall Height",    "ft", 0.5, null],
       ["par1","Parapet Height", "ft", 0.5, null]];
  const pressureFields = [
    ["pw",    "Wall Pressure",              "psf", 1, null],
    ["qWind", "Windward Parapet Pressure",  "psf", 1, null],
    ["qLee",  "Leeward Parapet Pressure",   "psf", 1, null],
  ];
  const FieldRows = (rows)=> rows.map(([w,label,unit,step,hint])=>(
    <div key={w} style={{ marginBottom:10 }}>
      <div style={{ display:"flex", alignItems:"center", justifyContent:"space-between", gap:10 }}>
        <label style={{ fontSize:13, fontWeight:600, color:"var(--ink)" }}>{label}</label>
        <div style={{ display:"flex", alignItems:"center", gap:6 }}>
          <input type="number" step={step} min={0} value={buf[w] ?? ""}
                 onChange={(e)=>write(w, e.target.value)} style={inputS}/>
          <span style={{ fontSize:12, color:"var(--muted)", width:26 }}>{unit}</span>
        </div>
      </div>
      {hint && <div style={{ fontSize:10.5, color:"var(--muted)", marginTop:2, lineHeight:1.35 }}>{hint}</div>}
    </div>
  ));
  return (
    <div className="ovl" onPointerDown={(e)=>{ if(e.target.classList.contains("ovl")) onClose(); }}>
      <div className="win" style={{ width:"min(420px,97vw)" }}>
        <div className="win-h">
          <div className="win-t">Global Inputs{twoStory ? " — 2-Story" : ""}</div>
          <button className="win-x" onClick={onClose} title="Close">×</button>
        </div>
        <div className="win-b">
          <div style={{ fontSize:11, color:"var(--muted)", marginBottom:14, lineHeight:1.45 }}>
            Set wall height, parapet height, and wind pressures for the whole building at once. Applying
            overwrites these fields on every wall — open a section cut afterward to fine-tune one wall.
            {twoStory && <> Parapet heights route by level: the 1st-Level value goes to walls tagged <b>1-story</b>, the 2nd-Level value to the full-height 2-story walls.</>}
          </div>
          <div style={subH}>Wall &amp; parapet heights</div>
          {FieldRows(heightFields)}
          <div style={{ ...subH, marginTop:14 }}>Wind pressures</div>
          {FieldRows(pressureFields)}
          <div style={{ display:"flex", gap:8, marginTop:14, paddingTop:12, borderTop:"1px solid var(--line)" }}>
            <button onClick={onClose}
              style={{ flex:"0 0 auto", padding:"8px 14px", border:"1px solid var(--line)", background:"#FFFFFF",
                       color:"var(--ink)", borderRadius:4, fontWeight:600, cursor:"pointer" }}>Cancel</button>
            <button onClick={()=>onApply(buf)}
              style={{ flex:1, padding:"8px 14px", border:"1.5px solid var(--accent)", background:"var(--accent)",
                       color:"#FFFFFF", borderRadius:4, fontWeight:700, cursor:"pointer" }}>Apply to all walls</button>
          </div>
        </div>
      </div>
    </div>
  );
}

function PlanSketcher({ onDesignShearWalls, fileOps, registerProject, twoStory, setTwoStory, activeFloor, setActiveFloor, g, setGl, setWtotal }) {
  const [graph,    setGraph]    = useState(INIT.graph);
  const [selected, setSelected] = useState(null);
  const [menu,     setMenu]     = useState(null);
  const [dlEdit,   setDlEdit]   = useState(null);   // (rev 49) edge key whose DL-tributary window is open, or null
  const [globalInputs,setGlobalInputs]=useState(null); // (rev 56) Global Inputs window: null = closed; {H,H2,par1,par2,pw,qWind,qLee} seed = open
  const [dimEdit,  setDimEdit]  = useState(null);
  const [sections, setSections] = useState({h:null, v:null}); // {axis,sign} per orientation
  const [wallProps,setWallProps]= useState({});      // edge key -> {H,pw,qWind,qLee,parW,parL}
  const [activeWall,setActiveWall]=useState(null);   // {axis,key} | null — wall being edited
  const [draft,    setDraft]    = useState(null);    // live cut line being drawn
  const [noSupport,setNoSupport]= useState(()=>new Set()); // edge keys NOT taking point load
  const [oneStory, setOneStory] = useState(()=>new Set()); // (2-story mode) edge keys that are ONLY 1 story — they
                                                           // touch the floor diaphragm but not the roof diaphragm.
  const [snapOn,   setSnapOn]   = useState(true);
  const [ortho,    setOrtho]    = useState(true);
  const [dims,     setDims]     = useState(true);
  const [markScale,setMarkScale]= useState(1);       // on-plan MARKUP scale (toolbar ▸ Markup): scales text labels, load/reaction arrows, AND nodes together — 1 / .75 / .5 / .25 — so markup doesn't blanket a zoomed-out plan
  const [loadCase, setLoadCase] = useState("wind");  // (rev 59) on-plan load VIEW: "wind" (section-cut wind loads) or "seismic" (V/extent boundary loads, both directions)
  const [panMode,  setPanMode]  = useState(false);   // left-drag "hand" pan tool (from canvas menu)
  const [zoomEnabled,setZoomEnabled]=useState(true); // wheel-zoom master switch (canvas-menu light)
  const [panCursor,setPanCursor]=useState(false);    // true while a pan gesture is live (grab cursor)

  const svgRef   = useRef(null);
  const stageRef = useRef(null);
  const menuRef  = useRef(null);
  const idc      = useRef(INIT.nextId);
  const history  = useRef([]);
  const future   = useRef([]);   // redo stack

  const nodeDrag = useRef(null);
  const wallDrag = useRef(null);
  const secDraw  = useRef(null);   // {sx,sy,su,moved}
  const panRef   = useRef(null);   // middle-button pan gesture {sx,sy,view}
  const panModeRef = useRef(panMode);
  const zoomEnabledRef = useRef(zoomEnabled);
  const dimWrapRef = useRef(null);
  const pendingOpen = useRef(null); // axis to open after a fresh cut
  const activeWin = activeWall ? activeWall.axis : null;

  const graphRef = useRef(graph);
  const selRef   = useRef(selected);
  const sectionsRef = useRef(sections);
  useEffect(()=>{graphRef.current=graph;},[graph]);
  useEffect(()=>{selRef.current=selected;},[selected]);
  useEffect(()=>{sectionsRef.current=sections;},[sections]);
  useEffect(()=>{panModeRef.current=panMode;},[panMode]);
  useEffect(()=>{zoomEnabledRef.current=zoomEnabled;},[zoomEnabled]);

  const nodeById  = useCallback(id => graphRef.current.nodes.find(n=>n.id===id), []);
  const snapshot  = useCallback(()=>{
    history.current.push({graph:graphRef.current, sel:selRef.current});
    if (history.current.length>60) history.current.shift();
    future.current=[];                                   // a new action invalidates redo
  },[]);
  const undo = useCallback(()=>{
    const h=history.current.pop();
    if(h){ future.current.push({graph:graphRef.current, sel:selRef.current});
           setGraph(h.graph);setSelected(h.sel);setDimEdit(null); }
  },[]);
  const redo = useCallback(()=>{
    const f=future.current.pop();
    if(f){ history.current.push({graph:graphRef.current, sel:selRef.current});
           setGraph(f.graph);setSelected(f.sel);setDimEdit(null); }
  },[]);
  const toUser = useCallback(e=>{
    const svg=svgRef.current, pt=svg.createSVGPoint();
    pt.x=e.clientX; pt.y=e.clientY;
    return pt.matrixTransform(svg.getScreenCTM().inverse());
  },[]);
  // ── dynamic drawing space: viewBox auto-fits the plan; sizes scale with it ──
  const fit = useMemo(()=>{
    const ns=graph.nodes;
    let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
    ns.forEach(p=>{minX=Math.min(minX,p.x);minY=Math.min(minY,p.y);maxX=Math.max(maxX,p.x);maxY=Math.max(maxY,p.y);});
    if(draft){ minX=Math.min(minX,draft.x1,draft.x2); minY=Math.min(minY,draft.y1,draft.y2);
               maxX=Math.max(maxX,draft.x1,draft.x2); maxY=Math.max(maxY,draft.y1,draft.y2); }
    if(!isFinite(minX)) return {x:0,y:0,w:VB_W,h:VB_H};
    const span=Math.max(maxX-minX, maxY-minY, 20);
    const pad=Math.max(span*0.32, 10);   // margin leaves room for load arrows + labels
    return {x:minX-pad, y:minY-pad, w:(maxX-minX)+2*pad, h:(maxY-minY)+2*pad};
  },[graph,draft]);
  const draggingRef = useRef(false);
  const SRef = useRef(1);   // graphic scale, kept fresh each render (used by draw-mode hit radius)
  const [frozenView, setFrozenView] = useState(null);   // held steady during a drag
  // userView = an explicit, persistent viewBox the user has set (wheel-zoom, middle-drag pan, or by
  // drawing). null ⇒ auto-fit to the plan. While idle it takes precedence over auto-fit, so adding
  // nodes no longer re-frames/zooms the canvas on every click. The "Fit" button clears it (auto-fit).
  const [userView, setUserView] = useState(null);
  const fitRef = useRef(fit);
  useEffect(()=>{ fitRef.current=fit; if(!draggingRef.current) setFrozenView(null); },[fit]);
  const view = frozenView || userView || fit;
  const viewRef = useRef(view); viewRef.current = view;             // current viewBox, fresh each render
  const userViewRef = useRef(userView); useEffect(()=>{userViewRef.current=userView;},[userView]);
  // freeze the CURRENT view (including any manual zoom/pan) for the duration of a drag gesture
  const freezeView = useCallback(()=>{ draggingRef.current=true; setFrozenView(viewRef.current); },[]);
  const thawView   = useCallback(()=>{ draggingRef.current=false; setFrozenView(null); },[]);
  // While dragging, if the pointer nears/passes the frozen view's edge, grow the view to keep it
  // in frame (live zoom-out). Without this the viewport caps how far one gesture can reach —
  // e.g. a wall couldn't be drawn past ~80 ft from the default preset. Self-stabilizing: each
  // event expands only enough to contain the pointer + margin.
  const expandViewTo = useCallback((u)=>{
    if(!draggingRef.current) return;
    setFrozenView(v=>{
      const cur = v || viewRef.current;
      const m = Math.max(cur.w, cur.h) * 0.05;
      const x0=Math.min(cur.x, u.x-m),       y0=Math.min(cur.y, u.y-m);
      const x1=Math.max(cur.x+cur.w, u.x+m), y1=Math.max(cur.y+cur.h, u.y+m);
      if(x0===cur.x && y0===cur.y && x1===cur.x+cur.w && y1===cur.y+cur.h) return v;
      return { x:x0, y:y0, w:x1-x0, h:y1-y0 };
    });
  },[]);
  const S = Math.max(view.w, view.h)/110;            // 1 ⇒ original feel; grows with plan
  SRef.current = S;                                   // draw-mode hit radius tracks zoom
  const gridStep = useMemo(()=>niceStep(Math.max(view.w,view.h)),[view]);
  const gridStepRef = useRef(gridStep);
  useEffect(()=>{gridStepRef.current=gridStep;},[gridStep]);

  // ── CAD-style navigation: wheel = zoom toward the cursor, "Fit" = zoom-to-extents ──
  // Both write to userView (the persistent manual view). Zoom limits keep the plan from
  // collapsing to a point or vanishing into the distance.
  const VMIN = 6, VMAX = WORLD * 3;                   // smallest / largest viewBox span (ft)
  const zoomAt = useCallback((cx, cy, factor)=>{
    const svg = svgRef.current; if(!svg) return;
    const pt = svg.createSVGPoint(); pt.x=cx; pt.y=cy;
    const u = pt.matrixTransform(svg.getScreenCTM().inverse());   // world point under the cursor
    const cur = viewRef.current;
    const aspect = cur.h / cur.w;
    let w = clamp(cur.w * factor, VMIN, VMAX);
    let h = w * aspect;                                            // preserve aspect exactly
    const fx = (u.x - cur.x) / cur.w, fy = (u.y - cur.y) / cur.h;  // cursor's fractional position
    setUserView({ x: u.x - fx*w, y: u.y - fy*h, w, h });          // keep that world point fixed
  },[]);
  // native non-passive wheel listener (React's onWheel is passive → can't preventDefault page scroll);
  // also swallow the middle-button mousedown so the browser's autoscroll puck doesn't appear on pan.
  useEffect(()=>{
    const svg = svgRef.current; if(!svg) return;
    const onWheel = (e)=>{ if(!zoomEnabledRef.current) return; e.preventDefault(); zoomAt(e.clientX, e.clientY, e.deltaY>0 ? 1.12 : 1/1.12); };
    const onMid   = (e)=>{ if(e.button===1) e.preventDefault(); };
    svg.addEventListener("wheel", onWheel, { passive:false });
    svg.addEventListener("mousedown", onMid);
    return ()=>{ svg.removeEventListener("wheel", onWheel); svg.removeEventListener("mousedown", onMid); };
  },[zoomAt]);
  const zoomToFit = useCallback(()=>{ setUserView(null); },[]);   // back to auto-fit (zoom extents)
  // grow the persistent view just enough to contain a point (grow only — never recenters or zooms
  // in), so a node placed/dragged toward the edge while drawing stays visible without a jump.
  const growUserViewTo = useCallback((px,py)=>{
    setUserView(v=>{
      const cur = v || viewRef.current;
      const m = Math.max(cur.w, cur.h) * 0.06;
      const x0=Math.min(cur.x, px-m),       y0=Math.min(cur.y, py-m);
      const x1=Math.max(cur.x+cur.w, px+m), y1=Math.max(cur.y+cur.h, py+m);
      if(x0===cur.x && y0===cur.y && x1===cur.x+cur.w && y1===cur.y+cur.h) return v;
      return { x:x0, y:y0, w:x1-x0, h:y1-y0 };
    });
  },[]);

  const snap = useCallback(v=>{ const g=gridStepRef.current; return snapOn?Math.round(v/g)*g:Math.round(v*10)/10; },[snapOn]);
  const closeMenu = useCallback(()=>setMenu(null),[]);

  // Write values to the wall they physically belong to. target "self" = the active windward wall;
  // target "lee" = its back (leeward) wall, resolved live so a split back wall takes the segment
  // sitting behind this cut. One parapet per wall means no cross-syncing is needed.
  const setVals = useCallback((target, patch)=>{
    // (rev 49) An EXPLICIT edge key (the DL-tributary window, or a section-cut interior block wall)
    // edits that wall directly and does NOT require an open section cut. "self"/"lee" are relative to
    // the active windward wall, so they still do. (Pre-rev-49 this early-returned on no activeWall,
    // which would have silently dropped the DL writes opened straight from the wall menu.)
    const explicit = target && target!=="self" && target!=="lee";
    if(!explicit && !activeWall) return;
    let key = explicit ? target : activeWall.key;
    if(target==="lee"){
      const sign = sectionsRef.current[activeWall.axis] && sectionsRef.current[activeWall.axis].sign;
      key = findLeewardPartner(activeWall.key, activeWall.axis, sign, graphRef.current, activeWall.sAcross);
    }
    if(!key) return;
    setWallProps(m=>({ ...m, [key]:{ ...(m[key]||DEF_SECTION), ...patch } }));
  },[activeWall]);

  // ── set wall length (LENGTHEN semantics) ──
  // moveEnd "a"|"b": which endpoint moves; the other anchors. Chosen by which side of the
  // dimension the user clicked (nearest end moves, like AutoCAD's LENGTHEN); ties broken by
  // anchoring the better-connected end so the rest of the plan stays put.
  const applyWallLength = useCallback((edge, newLen, moveEnd="b")=>{
    if(!(newLen>0)) return;
    const g=graphRef.current;
    const a=g.nodes.find(n=>n.id===edge.a), b=g.nodes.find(n=>n.id===edge.b);
    if(!a||!b) return;
    const fixed = moveEnd==="a" ? b : a;          // anchored end
    const moved = moveEnd==="a" ? a : b;          // end that slides along the wall direction
    let dx=moved.x-fixed.x, dy=moved.y-fixed.y, L=Math.hypot(dx,dy);
    if(L<1e-6){dx=1;dy=0;L=1;}
    const nx=clamp(fixed.x+(dx/L)*newLen,-WORLD,WORLD);
    const ny=clamp(fixed.y+(dy/L)*newLen,-WORLD,WORLD);
    const movedId = moved.id;
    snapshot();
    setGraph(g=>{
      const nodes=g.nodes.map(n=>n.id===movedId?{...n,x:nx,y:ny}:n);
      if(ortho){
        for(const ed of g.edges){
          if(same(ed,edge)) continue;
          if(ed.a!==movedId&&ed.b!==movedId) continue;
          const othId=ed.a===movedId?ed.b:ed.a;
          const oth=g.nodes.find(n=>n.id===othId);
          const axis=edgeAxis(moved,oth);
          const i=nodes.findIndex(n=>n.id===othId);
          if(i>=0){nodes[i]={...nodes[i]};if(axis==="h")nodes[i].y=ny;else nodes[i].x=nx;}
        }
      }
      return{...g,nodes};
    });
    setDimEdit(null);
  },[snapshot,ortho]);

  // ── DRAW MODE — click to place straight wall segments (no curves) ──
  // First click anchors a node; each next click adds a node + wall, chaining like a polyline.
  // Clicking an existing node snaps to it (node snap beats ortho, CAD-style) so loops close
  // exactly. Ortho constrains each segment to H/V from the anchor; grid snap applies as usual.
  // Right-click ends the chain (stays in draw mode); Esc ends the chain, then exits the mode.
  const [drawMode, setDrawMode] = useState(false);
  const [drawAnchor, setDrawAnchor] = useState(null);   // node id the next wall starts from
  const [drawPrev, setDrawPrev] = useState(null);       // rubber-band preview point
  const [drawLenEdit, setDrawLenEdit] = useState(null); // (rev 71) Tab dynamic-length input {px,py,dir,val}
  const [cursorFt, setCursorFt] = useState(null);       // status-bar coordinates (ft)
  const [healNote, setHealNote] = useState(null);       // (rev 68) #stray edges repaired on the last load (toast), else null
  useEffect(()=>{ if(healNote==null) return; const t=setTimeout(()=>setHealNote(null), 7000); return ()=>clearTimeout(t); },[healNote]);
  const cursorRef = useRef(null);
  const drawModeRef = useRef(drawMode);   useEffect(()=>{drawModeRef.current=drawMode;},[drawMode]);
  const drawAnchorRef = useRef(drawAnchor); useEffect(()=>{drawAnchorRef.current=drawAnchor;},[drawAnchor]);
  const drawPrevRef = useRef(drawPrev);   useEffect(()=>{drawPrevRef.current=drawPrev;},[drawPrev]);          // (rev 71) Tab reads the live rubber-band heading off a ref (keydown closure stays stable)
  const drawLenEditRef = useRef(drawLenEdit); useEffect(()=>{drawLenEditRef.current=drawLenEdit;},[drawLenEdit]);
  // (rev 71) TOUCH / PINCH bookkeeping — all of this is gated on pointerType==="touch", so the mouse
  // path is byte-unchanged. touchPts tracks live touch points (id→client xy); pinchRef holds the
  // gesture frame once a 2nd finger lands; pendingTapRef defers draw-placement to lift (so a 2nd
  // finger can promote a tap into a pinch instead of dropping a stray node).
  const touchPts = useRef(new Map());
  const pinchRef = useRef(null);
  const pendingTapRef = useRef(null);

  // resolve a pointer event to a draw target, in priority order:
  //   1. an existing node within the pick radius → snap to it (closes loops exactly, beats ortho);
  //   2. (rev 66) the BODY of an existing wall within the pick radius → snap to the foot of the
  //      perpendicular and flag that wall for auto-split (so a click directly on a wall creates an
  //      intersection node there and splits the wall — same end-topology as the rev-64 drag bind);
  //   3. a free point, with ortho + grid snap as usual.
  const resolveDrawPoint = useCallback((e)=>{
    const u=toUser(e), g=graphRef.current;
    const R=2.4*SRef.current;
    // 1) existing-node snap — highest priority
    let nearest=null, best=R*R;
    g.nodes.forEach(n=>{ const d=(n.x-u.x)**2+(n.y-u.y)**2; if(d<best){best=d; nearest=n;} });
    if(nearest) return { node:nearest, x:nearest.x, y:nearest.y, snapped:true, splitEdge:null };
    // 2) wall-body snap — click landed on a wall line, not a node: target it for auto-split.
    //    Skip any wall the current anchor already joins (splitting one would make a sliver chain
    //    edge) — mirrors bindNodeToWall's incident-edge exclusion. Foot must be strictly interior
    //    (endpoints are node-snap territory, handled in step 1).
    const anchorId=drawAnchorRef.current;
    let bestW=null;
    for(const ed of g.edges){
      if(anchorId!==null && (ed.a===anchorId||ed.b===anchorId)) continue;
      const a=g.nodes.find(n=>n.id===ed.a), b=g.nodes.find(n=>n.id===ed.b);
      if(!a||!b) continue;
      const pr=projToSeg(u,a,b);
      if(pr.t<=1e-3||pr.t>=1-1e-3) continue;
      if(pr.dist>R) continue;
      if(!bestW||pr.dist<bestW.dist) bestW={edge:ed, pt:pr.pt, dist:pr.dist};
    }
    if(bestW) return { node:null, x:bestW.pt.x, y:bestW.pt.y, snapped:true, splitEdge:bestW.edge };
    // 3) free point — ortho + grid snap
    let x=u.x, y=u.y;
    const anchor = anchorId!==null ? g.nodes.find(n=>n.id===anchorId) : null;
    if(ortho && anchor){ if(Math.abs(u.x-anchor.x)>=Math.abs(u.y-anchor.y)) y=anchor.y; else x=anchor.x; }
    x=clamp(snap(x),-WORLD,WORLD); y=clamp(snap(y),-WORLD,WORLD);
    return { node:null, x, y, snapped:false, splitEdge:null };
  },[toUser,ortho,snap]);

  const placeDrawPoint = useCallback((e)=>{
    const pt=resolveDrawPoint(e);
    const anchorId=drawAnchorRef.current;
    growUserViewTo(pt.x, pt.y);          // keep the placed node in frame (grow only, never recenter)
    snapshot();
    // (rev 66) AUTO-SPLIT on draw: the click landed on a wall body. Create the intersection node
    // exactly on that wall, split the wall into two halves at the node, propagate the wall's
    // per-edge state to BOTH halves, and chain the anchor → new node — all in ONE setGraph (one
    // undo reverts the whole gesture). The new node now joins the two halves + the incoming wall,
    // so moving it later drags all of them. Mirrors bindNodeToWall's split/propagation, but the
    // split vertex is a fresh node placed by the draw click (not a dragged existing node).
    if(pt.splitEdge){
      const se=pt.splitEdge;
      const newId=idc.current++;
      setGraph(g=>{
        const edge=g.edges.find(ed=>same(ed,se));   // re-find in the live graph
        let nodes=[...g.nodes,{id:newId,x:pt.x,y:pt.y}];
        let edges=g.edges;
        if(edge){
          const e1=norm(edge.a,newId), e2=norm(newId,edge.b);
          edges=edges.filter(ed=>!same(ed,edge));
          if(!edges.some(ed=>same(ed,e1))) edges=[...edges,e1];
          if(!edges.some(ed=>same(ed,e2))) edges=[...edges,e2];
        }
        if(anchorId!==null && anchorId!==newId){
          const ne=norm(anchorId,newId);
          if(!edges.some(ed=>same(ed,ne))) edges=[...edges,ne];
        }
        return { nodes, edges };
      });
      const e1=norm(se.a,newId), e2=norm(newId,se.b);
      const pk=keyOf(se), k1=keyOf(e1), k2=keyOf(e2);
      setNoSupport(s=>{ if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(k1); n.add(k2); return n; });
      setOneStory(s=>{ if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(k1); n.add(k2); return n; });
      setWallProps(m=>{ if(!m[pk]) return m; const v=m[pk]; const n={...m}; n[k1]={...v}; n[k2]={...v}; delete n[pk]; return n; });
      setDrawAnchor(newId);
      return;
    }
    setGraph(g=>{
      let nodes=g.nodes, edges=g.edges, targetId;
      if(pt.node) targetId=pt.node.id;
      else { targetId=idc.current++; nodes=[...nodes,{id:targetId,x:pt.x,y:pt.y}]; }
      if(anchorId!==null && anchorId!==targetId){
        const ne=norm(anchorId,targetId);
        if(!edges.some(ed=>same(ed,ne))) edges=[...edges,ne];
      }
      setDrawAnchor(targetId);
      return { nodes, edges };
    });
  },[resolveDrawPoint,snapshot,growUserViewTo]);

  const endDrawChain = useCallback(()=>setDrawAnchor(null),[]);

  // (rev 71) DYNAMIC LENGTH (AutoCAD-style): while drawing, Tab opens a length box; Enter commits the
  // next node EXACTLY `len` ft from the anchor along the captured rubber-band heading (a typed length
  // overrides osnap, like AutoCAD). Mirrors placeDrawPoint's non-split chaining branch, but the
  // endpoint is computed from anchor+dir·len instead of the cursor, and it never auto-splits a wall.
  const commitDrawLength = useCallback((len)=>{
    const le = drawLenEditRef.current;
    const anchorId = drawAnchorRef.current;
    if(!le || anchorId==null || !(len>0)){ setDrawLenEdit(null); return; }
    const g = graphRef.current;
    const anchor = g.nodes.find(n=>n.id===anchorId);
    if(!anchor){ setDrawLenEdit(null); return; }
    const p = pointAtLength(anchor, le.dir, len);
    const nx = clamp(p.x,-WORLD,WORLD), ny = clamp(p.y,-WORLD,WORLD);
    growUserViewTo(nx,ny);             // keep the new node in frame (grow only)
    snapshot();
    const newId = idc.current++;
    setGraph(gg=>{
      const nodes=[...gg.nodes,{id:newId,x:nx,y:ny}];
      let edges=gg.edges;
      const ne=norm(anchorId,newId);
      if(!edges.some(ed=>same(ed,ne))) edges=[...edges,ne];
      return { nodes, edges };
    });
    setDrawAnchor(newId);              // chain continues from the new node
    setDrawLenEdit(null);
  },[snapshot,growUserViewTo]);

  // ── PROJECT SERIALIZATION — the shell saves/loads the whole suite; we expose our slice ──
  useEffect(()=>{
    if(!registerProject) return;
    registerProject({
      get: ()=>({ graph:sanitizeGraph(graphRef.current),   // (rev 68) never write an orphan/duplicate/self-loop edge to disk
                  wallProps, noSupport:[...noSupport], oneStory:[...oneStory], sections, nextId:idc.current,
                  // v2: the camera + working state, so a reopened file looks like where you left it
                  view:viewRef.current, selected:selRef.current,
                  drawMode:drawModeRef.current, panMode:panModeRef.current,
                  zoomEnabled:zoomEnabledRef.current, snapOn, ortho, dims, markScale, loadCase }),
      set: (s)=>{
        if(!s||!s.graph) return;
        const cleanGraph = sanitizeGraph(s.graph);   // (rev 67) self-heal orphan/duplicate/self-loop edges from any older save
        const healed = (Array.isArray(s.graph.edges)?s.graph.edges.length:0) - cleanGraph.edges.length;
        setGraph(cleanGraph);
        setHealNote(healed>0 ? healed : null);        // (rev 68) one-time toast when a loaded file was repaired

        setWallProps(s.wallProps||{});
        setNoSupport(new Set(s.noSupport||[]));
        setOneStory(new Set(s.oneStory||[]));   // old files lack it → no 1-story walls (unchanged behavior)
        setSections(s.sections||{h:null,v:null});
        idc.current = s.nextId || (Math.max(0,...s.graph.nodes.map(n=>n.id))+1);
        // transient editors never auto-reopen (modal wind window + inline dim editor)
        setActiveWall(null); setDimEdit(null); setMenu(null); setDrawPrev(null); setDrawAnchor(null); setDlEdit(null);
        setDrawLenEdit(null); pendingTapRef.current=null; pinchRef.current=null; touchPts.current.clear();   // (rev 71) drop any transient draw/touch state on load
        // v2 restores the saved camera + toggles + selection; v1/New (no view) reverts to auto-fit + defaults
        setUserView(s.view || null); setFrozenView(null);
        setSelected("selected" in s ? s.selected : null);
        setDrawMode(!!s.drawMode);
        setPanMode(!!s.panMode);
        setZoomEnabled("zoomEnabled" in s ? !!s.zoomEnabled : true);
        if("snapOn" in s) setSnapOn(!!s.snapOn);
        if("ortho" in s) setOrtho(!!s.ortho);
        if("dims" in s) setDims(!!s.dims);
        if("markScale" in s) setMarkScale(Number(s.markScale)||1);
        if("loadCase" in s) setLoadCase(s.loadCase==="seismic"?"seismic":"wind");
        else if("textScale" in s) setMarkScale(Number(s.textScale)||1);   // rev 30 key — back-compat
        history.current=[]; future.current=[];
        setPushedSig(null);                          // rev 130: New/Open → no stale-push warning until the next push (a loaded file is in sync with its own saved design)
      },
      // rev 24: let the Design tab rebuild geometry-less (stale) lines straight from the restored
      // plan. `rerun` is runDesignHandoff (regenerates geometry-complete lines from the live graph);
      // `hasReactions` says whether a rerun would actually produce any (a cut must exist). Both are
      // captured fresh because this effect has no dep array and re-registers on every render.
      rerun: runDesignHandoff,
      hasReactions: !!((secH && secH.reactions && secH.reactions.length) || (secV && secV.reactions && secV.reactions.length)),
      undo, redo,   // (rev 70) promoted to the app-level toolbar; re-registered every render so they stay current
    });
  });
  const toggleDrawMode = useCallback(()=>{
    const turningOn = !drawModeRef.current;
    // entering Draw freezes the current framing (seed userView) so each click stops re-fitting the
    // canvas; the view then only grows when you draw past its edge, or when you wheel-zoom / pan.
    if(turningOn && userViewRef.current==null) setUserView(viewRef.current);
    if(turningOn) setPanMode(false);                 // Draw and Pan are mutually exclusive
    setDrawMode(turningOn); setDrawAnchor(null); setDrawPrev(null); setMenu(null); setDimEdit(null);
  },[]);
  // PAN tool: a left-drag hand tool (complements middle-drag pan, for trackpad/no-middle-button
  // users). Mutually exclusive with Draw. Reached from the empty-area right-click "Canvas" menu.
  const togglePanMode = useCallback(()=>{
    const turningOn = !panModeRef.current;
    if(turningOn){ setDrawMode(false); setDrawAnchor(null); setDrawPrev(null); }
    setPanMode(turningOn); setMenu(null); setDimEdit(null);
  },[]);

  // ── DELETE ── (sections recompute from geometry; nothing to unbind)
  const deleteNode = useCallback(id=>{
    snapshot();
    setGraph(g=>({ nodes:g.nodes.filter(n=>n.id!==id), edges:g.edges.filter(e=>e.a!==id&&e.b!==id) }));
    setSelected(s=>s===id?null:s);
    setDimEdit(null);
  },[snapshot]);

  const deleteEdge = useCallback(edge=>{
    snapshot();
    setGraph(g=>({...g, edges:g.edges.filter(e=>!same(e,edge))}));
    setDimEdit(null);
  },[snapshot]);

  // ── SPLIT a wall ──
  const splitWall = useCallback((edge, u)=>{
    const g=graphRef.current;
    const a=g.nodes.find(n=>n.id===edge.a), b=g.nodes.find(n=>n.id===edge.b);
    if(!a||!b) return;
    let x=clamp(snap(u.x),-WORLD,WORLD), y=clamp(snap(u.y),-WORLD,WORLD);
    if(edgeAxis(a,b)==="h") y=a.y; else x=a.x;
    const id=idc.current++;
    const e1=norm(edge.a,id), e2=norm(id,edge.b);
    const newGraph={ nodes:[...g.nodes,{id,x,y}], edges:g.edges.filter(e=>!same(e,edge)).concat([e1,e2]) };
    snapshot();
    setGraph(newGraph);
    setNoSupport(s=>{ const pk=keyOf(edge); if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(keyOf(e1)); n.add(keyOf(e2)); return n; });
    setOneStory(s=>{ const pk=keyOf(edge); if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(keyOf(e1)); n.add(keyOf(e2)); return n; });
    setWallProps(m=>{ const pk=keyOf(edge); if(!m[pk]) return m; const v=m[pk]; const n={...m}; n[keyOf(e1)]={...v}; n[keyOf(e2)]={...v}; delete n[pk]; return n; });
    setSelected(id);
  },[snap,snapshot]);

  // ── (rev 64) AUTO-SPLIT on a T-intersection ──
  // When a dragged node is dropped on the BODY of another wall, bind it there: snap the node
  // exactly onto that wall, split the wall into two segments at the node, and carry the wall's
  // per-edge state (support flag, 1-story tag, section props) onto BOTH halves. The node then
  // joins all three walls, so moving it later drags the split wall with it. Mirrors splitWall's
  // three-way propagation, but the split vertex is the EXISTING dragged node (not a fresh id), so
  // the incoming wall stays attached. No extra snapshot() — the drag already pushed one history
  // entry, so a single undo reverts the whole drag-and-bind gesture.
  const bindNodeToWall = useCallback((nodeId)=>{
    const g=graphRef.current;
    const node=g.nodes.find(n=>n.id===nodeId);
    if(!node) return;
    const tol=2.4*SRef.current;          // same pick radius the draw tool uses for node snapping
    let best=null;
    for(const e of g.edges){
      if(e.a===nodeId||e.b===nodeId) continue;      // can't split a wall this node already joins
      const a=g.nodes.find(n=>n.id===e.a), b=g.nodes.find(n=>n.id===e.b);
      if(!a||!b) continue;
      const pr=projToSeg(node,a,b);
      if(pr.t<=1e-3||pr.t>=1-1e-3) continue;         // foot must be on the body, not at an endpoint
      if(pr.dist>tol) continue;
      if(!best||pr.dist<best.dist) best={edge:e, pt:pr.pt, dist:pr.dist};
    }
    if(!best) return;
    const e1=norm(best.edge.a,nodeId), e2=norm(nodeId,best.edge.b);
    if(same(e1,e2)) return;                          // degenerate guard (excluded by the t test anyway)
    const nodes=g.nodes.map(n=>n.id===nodeId?{...n,x:best.pt.x,y:best.pt.y}:n);
    let edges=g.edges.filter(e=>!same(e,best.edge));
    if(!edges.some(e=>same(e,e1))) edges=[...edges,e1];
    if(!edges.some(e=>same(e,e2))) edges=[...edges,e2];
    setGraph({nodes,edges});
    const pk=keyOf(best.edge), k1=keyOf(e1), k2=keyOf(e2);
    setNoSupport(s=>{ if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(k1); n.add(k2); return n; });
    setOneStory(s=>{ if(!s.has(pk)) return s; const n=new Set(s); n.delete(pk); n.add(k1); n.add(k2); return n; });
    setWallProps(m=>{ if(!m[pk]) return m; const v=m[pk]; const n={...m}; n[k1]={...v}; n[k2]={...v}; delete n[pk]; return n; });
  },[]);

  const connectTo = useCallback((fromId, toId)=>{
    if(graphRef.current.edges.some(e=>same(e,norm(fromId,toId)))) return;
    snapshot();
    setGraph(g=>({...g, edges:[...g.edges, norm(fromId,toId)]}));
  },[snapshot]);

  const loadPreset = name=>{
    snapshot();
    const r=buildFrom(PRESETS[name],idc.current);
    idc.current=r.nextId;
    setGraph(r.graph); setSelected(null); setDimEdit(null); setSections({h:null,v:null}); setActiveWall(null); setWallProps({}); setDlEdit(null);
    setUserView(null);   // frame the new preset (zoom-to-extents)
  };
  const clearAll=()=>{ snapshot(); setGraph({nodes:[],edges:[]}); setSelected(null); setDimEdit(null); setSections({h:null,v:null}); setActiveWall(null); setWallProps({}); setUserView(null); setDlEdit(null); };

  const removeSection = ()=>{ if(activeWin){ setSections(s=>({...s,[activeWin]:null})); setActiveWall(null); } };
  // reverse wind: flip the section's travel direction and re-point the elevation window to the
  // NEW windward wall — identical to dragging a fresh cut the other way. Each wall owns its own
  // parapet height, so values persist and simply swap windward/leeward roles (no copying).
  const reverseWind = ()=>{
    if(!activeWin) return;
    // remember the across-wind position of the current cut so the flip re-opens the segment that
    // sits at that same position on the new windward side (the old leeward, which may be split).
    let sAcross=null;
    if(activeWall){
      const e=graphRef.current.edges.find(x=>keyOf(x)===activeWall.key);
      if(e){ const a=graphRef.current.nodes.find(n=>n.id===e.a), b=graphRef.current.nodes.find(n=>n.id===e.b);
        if(a&&b) sAcross = activeWin==="v" ? (a.x+b.x)/2 : (a.y+b.y)/2; }
    }
    setSections(s=> s[activeWin]?{...s,[activeWin]:{...s[activeWin],sign:-s[activeWin].sign}}:s);
    pendingOpen.current = { axis:activeWin, sAcross };   // re-open matching segment after recompute
  };

  // ── CONTEXT MENU ──
  const openMenu = useCallback((e, payload)=>{
    e.preventDefault(); e.stopPropagation();
    setDimEdit(null);
    const r=stageRef.current.getBoundingClientRect();
    let x=e.clientX-r.left, y=e.clientY-r.top;
    x=Math.min(x, r.width-160); y=Math.min(y, r.height-100);
    const u=toUser(e);
    setMenu({...payload, x:Math.max(4,x), y:Math.max(4,y), u});
  },[toUser]);

  useEffect(()=>{
    if(!dimEdit) return;
    const h=e=>{
      if(dimWrapRef.current&&dimWrapRef.current.contains(e.target)) return;
      if(e.button===2){ setDimEdit(null); return; }
      const v=parseFloat(dimEdit.val);
      if(v>0) applyWallLength(dimEdit.edge,v,dimEdit.moveEnd); else setDimEdit(null);
    };
    window.addEventListener("pointerdown",h,true);
    return()=>window.removeEventListener("pointerdown",h,true);
  },[dimEdit, applyWallLength]);

  useEffect(()=>{
    if(!menu) return;
    const h=e=>{ if(menuRef.current&&menuRef.current.contains(e.target)) return; setMenu(null); };
    window.addEventListener("pointerdown",h);
    return()=>window.removeEventListener("pointerdown",h);
  },[menu]);

  useEffect(()=>{
    const h=e=>{
      if(e.key==="Escape"){
        if(drawLenEditRef.current){ setDrawLenEdit(null); return; }   // (rev 71) Esc closes the length box first (chain stays)
        if(drawModeRef.current){
          if(drawAnchorRef.current!==null) setDrawAnchor(null);
          else { setDrawMode(false); setDrawPrev(null); }
          return;
        }
        setSelected(null);setMenu(null);setDimEdit(null);setActiveWall(null);setPanMode(false);setDlEdit(null);
      }
      // (rev 71) Tab while drawing → open the dynamic-length box, seeded with the live rubber-band
      // length + heading. Requires an active chain (anchor placed) and a preview point. preventDefault
      // stops Tab from moving focus. Guarded so Tab inside the open box doesn't reopen it.
      else if(e.key==="Tab" && drawModeRef.current && drawAnchorRef.current!==null
              && drawPrevRef.current && !drawLenEditRef.current){
        e.preventDefault();
        const g=graphRef.current;
        const anchor=g.nodes.find(n=>n.id===drawAnchorRef.current);
        const pv=drawPrevRef.current;
        if(!anchor||!pv) return;
        const dir={dx:pv.x-anchor.x, dy:pv.y-anchor.y};
        const L=Math.hypot(dir.dx,dir.dy);
        if(!(L>1e-6)) return;                                // no heading yet (cursor on the anchor)
        let px=0, py=0;
        try{
          const m=svgRef.current.getScreenCTM(), r=stageRef.current.getBoundingClientRect();
          const sx=m.a*pv.x+m.c*pv.y+m.e, sy=m.b*pv.x+m.d*pv.y+m.f;
          px=sx-r.left; py=sy-r.top-22;
        }catch(_){}
        setDrawLenEdit({ px, py, dir, val:String(fmtHalf(L)) });
      }
      else if((e.key==="Delete"||e.key==="Backspace")&&selRef.current!==null){ e.preventDefault(); deleteNode(selRef.current); }
      else if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==="z"&&e.shiftKey){e.preventDefault();redo();}
      else if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==="z"){e.preventDefault();undo();}
      else if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==="y"){e.preventDefault();redo();}
      else if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==="s"){e.preventDefault();fileOps&&fileOps.onSave();}
      else if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==="o"){e.preventDefault();fileOps&&fileOps.onOpen();}
    };
    window.addEventListener("keydown",h);
    return()=>window.removeEventListener("keydown",h);
  },[deleteNode,undo,redo,fileOps]);

  // ── POINTER handlers ──
  // start a left-drag pan gesture (hand tool / pan mode). Reuses panRef (same path as middle-drag).
  const beginPan = useCallback(e=>{
    e.preventDefault(); e.stopPropagation();
    svgRef.current.setPointerCapture(e.pointerId);
    panRef.current={ sx:e.clientX, sy:e.clientY, view:viewRef.current };
    setPanCursor(true);
  },[]);
  // (rev 71) TOUCH: record a touch pointer; when a 2nd finger lands, promote to a pinch (abort any
  // in-flight single-finger gesture + pending tap, freeze the gesture frame). Returns true when the
  // event was consumed by entering pinch — every touch-capable down handler bails on true. Mouse/pen
  // events (pointerType!=="touch") return false instantly, so the desktop path is byte-unchanged.
  const touchTrack = useCallback(e=>{
    if(e.pointerType!=="touch") return false;
    touchPts.current.set(e.pointerId,{x:e.clientX,y:e.clientY});
    if(touchPts.current.size===2){
      nodeDrag.current=null; wallDrag.current=null; secDraw.current=null; setDraft(null);
      pendingTapRef.current=null;
      if(draggingRef.current) thawView();
      const pts=[...touchPts.current.values()];
      const mid={clientX:(pts[0].x+pts[1].x)/2, clientY:(pts[0].y+pts[1].y)/2};
      pinchRef.current={ view0:viewRef.current, d0:Math.hypot(pts[1].x-pts[0].x,pts[1].y-pts[0].y), midWorld:toUser(mid) };
      setPanCursor(false);
      return true;
    }
    return false;
  },[toUser,thawView]);
  // (rev 71) Draw-mode placement entry: a mouse click places immediately (unchanged); a touch TAP is
  // deferred to lift (pendingTapRef) with a live preview, so a quickly-following 2nd finger becomes a
  // pinch instead of dropping a stray node. Commit happens in onUp on a clean single-finger lift.
  const drawDown = useCallback(e=>{
    if(e.pointerType==="touch"){ pendingTapRef.current={x:e.clientX,y:e.clientY}; setDrawPrev(resolveDrawPoint(e)); }
    else placeDrawPoint(e);
  },[placeDrawPoint,resolveDrawPoint]);
  const onNodeLDown = useCallback((id,e)=>{
    if(e.button!==0) return;
    e.stopPropagation(); closeMenu();
    if(touchTrack(e)) return;                                // (rev 71) 2nd finger → pinch
    if(panModeRef.current){ beginPan(e); return; }          // pan tool: drag anywhere pans the view
    if(drawModeRef.current){ drawDown(e); return; }         // node snap: connect to this node (touch defers to lift)
    svgRef.current.setPointerCapture(e.pointerId);
    const me=graphRef.current.nodes.find(n=>n.id===id);
    const meta=ortho
      ? graphRef.current.edges.filter(ed=>ed.a===id||ed.b===id).map(ed=>{
          const oth=graphRef.current.nodes.find(n=>n.id===(ed.a===id?ed.b:ed.a));
          return{id:oth.id, axis:edgeAxis(me,oth)};
        })
      : [];
    nodeDrag.current={id, moved:false, sx:e.clientX, sy:e.clientY, meta};
    freezeView();
  },[closeMenu,ortho,freezeView,placeDrawPoint,beginPan,touchTrack,drawDown]);

  const onWallLDown = useCallback((edge,e)=>{
    if(e.button!==0) return;
    e.stopPropagation(); closeMenu();
    if(touchTrack(e)) return;                                // (rev 71) 2nd finger → pinch
    if(panModeRef.current){ beginPan(e); return; }          // pan tool: drag anywhere pans the view
    if(drawModeRef.current){ drawDown(e); return; }         // place a point even over a wall (touch defers to lift)
    svgRef.current.setPointerCapture(e.pointerId);
    const g=graphRef.current;
    const a=g.nodes.find(n=>n.id===edge.a), b=g.nodes.find(n=>n.id===edge.b);
    const u=toUser(e);
    wallDrag.current={aId:edge.a,bId:edge.b,ax:a.x,ay:a.y,bx:b.x,by:b.y, axis:edgeAxis(a,b), sux:u.x,suy:u.y, moved:false};
    freezeView();
  },[closeMenu,toUser,freezeView,placeDrawPoint,beginPan,touchTrack,drawDown]);

  // background drag = draw a section cut; middle-button drag (or pan tool) = pan (CAD-style)
  const onBgLDown = useCallback(e=>{
    if(e.button===1){                                       // middle button → pan the view
      e.preventDefault(); closeMenu();
      svgRef.current.setPointerCapture(e.pointerId);
      panRef.current={ sx:e.clientX, sy:e.clientY, view:viewRef.current };
      setPanCursor(true);
      return;
    }
    if(e.button!==0) return;
    closeMenu();
    if(touchTrack(e)) return;                                // (rev 71) 2nd finger → pinch
    if(panModeRef.current){ beginPan(e); return; }          // pan tool: left-drag pans the view
    if(drawModeRef.current){ drawDown(e); return; }         // draw mode: click places a node (touch defers to lift)
    svgRef.current.setPointerCapture(e.pointerId);
    secDraw.current={ su:toUser(e), sx:e.clientX, sy:e.clientY, moved:false };
    freezeView();
  },[closeMenu,toUser,freezeView,placeDrawPoint,beginPan,touchTrack,drawDown]);

  const onBgContextMenu = useCallback(e=>{
    e.preventDefault();
    if(drawModeRef.current){
      // Mid-draw: a first right-click still ends the active chain (unchanged muscle memory). Once
      // the chain is ended — or before one is started — right-click opens the Canvas menu, so
      // Draw / Pan / Zoom are reachable without leaving Draw mode.
      if(drawAnchorRef.current!==null){ endDrawChain(); return; }
      openMenu(e, { kind:"canvas" });
      return;
    }
    setSelected(null); setDimEdit(null);                    // right-click clears the selection (as before)
    openMenu(e, { kind:"canvas" });                         // …and opens the canvas tool menu
  },[endDrawChain,openMenu]);

  const onMove = useCallback(e=>{
    // (rev 71) TWO-FINGER PINCH/ZOOM-PAN — runs before every other gesture. Keeps the touch point
    // map fresh and, while a pinch is active, drives the view from the live finger spread + midpoint
    // (zoom) and the midpoint translation (pan), then bails so no single-finger logic runs.
    if(e.pointerType==="touch" && touchPts.current.has(e.pointerId)){
      touchPts.current.set(e.pointerId,{x:e.clientX,y:e.clientY});
    }
    if(pinchRef.current && touchPts.current.size>=2){
      const svg=svgRef.current; if(!svg) return;
      const pts=[...touchPts.current.values()];
      const d=Math.hypot(pts[1].x-pts[0].x, pts[1].y-pts[0].y);
      const cur={x:(pts[0].x+pts[1].x)/2, y:(pts[0].y+pts[1].y)/2};
      const p=pinchRef.current;
      setUserView(pinchTransform(p.view0, svg.getBoundingClientRect(), p.midWorld, cur, p.d0, d, VMIN, VMAX));
      return;
    }
    if(panRef.current){                                   // middle-button pan: translate the view
      const p=panRef.current, svg=svgRef.current; if(!svg) return;
      const r=svg.getBoundingClientRect();
      const dx=(e.clientX-p.sx)/r.width  * p.view.w;
      const dy=(e.clientY-p.sy)/r.height * p.view.h;
      setUserView({ x:p.view.x-dx, y:p.view.y-dy, w:p.view.w, h:p.view.h });
      return;
    }
    { const u=toUser(e);                                 // status-bar cursor readout
      const cx=Math.round(u.x*10)/10, cy=Math.round(u.y*10)/10;
      if(!cursorRef.current||cursorRef.current.x!==cx||cursorRef.current.y!==cy){
        cursorRef.current={x:cx,y:cy}; setCursorFt({x:cx,y:cy});
      } }
    if(drawModeRef.current && !nodeDrag.current && !wallDrag.current && !secDraw.current){
      setDrawPrev(resolveDrawPoint(e));                     // rubber-band / snap preview
      return;
    }
    if(nodeDrag.current||wallDrag.current||secDraw.current) expandViewTo(toUser(e));
    if(nodeDrag.current){
      const nd=nodeDrag.current;
      if(!nd.moved){ const dx=e.clientX-nd.sx, dy=e.clientY-nd.sy; if(dx*dx+dy*dy>36){nd.moved=true; snapshot();} }
      if(nd.moved){
        const u=toUser(e);
        const nx=clamp(snap(u.x),-WORLD,WORLD), ny=clamp(snap(u.y),-WORLD,WORLD);
        setGraph(g=>{
          const nodes=g.nodes.map(n=>n.id===nd.id?{...n,x:nx,y:ny}:n);
          if(ortho) for(const m of nd.meta){ const i=nodes.findIndex(n=>n.id===m.id); if(i>=0){nodes[i]={...nodes[i]};if(m.axis==="h")nodes[i].y=ny;else nodes[i].x=nx;} }
          return{...g,nodes};
        });
      }
      return;
    }
    if(wallDrag.current){
      const w=wallDrag.current, u=toUser(e);
      let dx=u.x-w.sux, dy=u.y-w.suy;
      if(ortho){if(w.axis==="h") dx=0; else dy=0;}
      if(snapOn){const g=gridStepRef.current; dx=Math.round(dx/g)*g; dy=Math.round(dy/g)*g;}
      dx=clamp(dx, -WORLD-Math.min(w.ax,w.bx), WORLD-Math.max(w.ax,w.bx));
      dy=clamp(dy, -WORLD-Math.min(w.ay,w.by), WORLD-Math.max(w.ay,w.by));
      if(!w.moved&&(dx||dy)){w.moved=true; snapshot();}
      if(w.moved) setGraph(g=>({...g, nodes:g.nodes.map(n=>
        n.id===w.aId?{...n,x:w.ax+dx,y:w.ay+dy}: n.id===w.bId?{...n,x:w.bx+dx,y:w.by+dy}:n)}));
      return;
    }
    if(secDraw.current){
      const sd=secDraw.current;
      if(!sd.moved){ const dx=e.clientX-sd.sx, dy=e.clientY-sd.sy; if(dx*dx+dy*dy>20) sd.moved=true; }
      if(sd.moved){ const u=toUser(e); setDraft({x1:sd.su.x,y1:sd.su.y,x2:u.x,y2:u.y}); }
    }
  },[snapshot,toUser,snap,ortho,snapOn,expandViewTo,resolveDrawPoint]);

  const onUp = useCallback(e=>{
    // (rev 71) TOUCH lift: drop the point; if a pinch was active, end it once <2 fingers remain (don't
    // resume a drag from the surviving finger). Otherwise, a deferred draw tap commits on a clean
    // single-finger lift (small movement). All touch-only — mouse falls straight through.
    if(e.pointerType==="touch"){
      touchPts.current.delete(e.pointerId);
      svgRef.current?.releasePointerCapture?.(e.pointerId);
      if(pinchRef.current){ if(touchPts.current.size<2) pinchRef.current=null; return; }
      if(pendingTapRef.current){
        const t=pendingTapRef.current; pendingTapRef.current=null;
        if(drawModeRef.current && Math.hypot(e.clientX-t.x, e.clientY-t.y) < 12) placeDrawPoint(e);
        return;
      }
    }
    svgRef.current?.releasePointerCapture?.(e.pointerId);
    if(panRef.current){ panRef.current=null; setPanCursor(false); return; }    // end pan (no thaw — pan doesn't freeze)
    thawView();
    if(nodeDrag.current){ const nd=nodeDrag.current; nodeDrag.current=null; if(nd.moved) bindNodeToWall(nd.id); return; }
    if(wallDrag.current){ wallDrag.current=null; return; }
    if(secDraw.current){
      const sd=secDraw.current; secDraw.current=null; setDraft(null);
      if(sd.moved){
        const u=toUser(e);
        const line={x1:sd.su.x,y1:sd.su.y,x2:u.x,y2:u.y};
        if(dist({x:line.x1,y:line.y1},{x:line.x2,y:line.y2})>4){
          const axis = Math.abs(line.x2-line.x1) >= Math.abs(line.y2-line.y1) ? "h" : "v";
          // wind travels in the drag direction (drag down = N→S, drag right = W→E)
          const sign = axis==="v" ? (line.y2>=line.y1?1:-1) : (line.x2>=line.x1?1:-1);
          // A valid section must pass through ≥2 across-wind (exterior) walls. The FIRST one the
          // cut crosses (lowest t — the drag starts on the windward side) is the EXACT windward
          // segment to open, so a cut through a split wall opens the segment it actually passes
          // through instead of always defaulting to the first segment of the line.
          const g=graphRef.current, p1={x:line.x1,y:line.y1}, p2={x:line.x2,y:line.y2};
          const recv = axis==="v" ? "h" : "v";          // across-wind walls = windward/leeward faces
          const hits=[];
          for(const ed of g.edges){
            const a=g.nodes.find(n=>n.id===ed.a), b=g.nodes.find(n=>n.id===ed.b);
            if(!a||!b||edgeAxis(a,b)!==recv) continue;
            const r=segInt(p1,p2,a,b);
            if(r) hits.push({ key:keyOf(ed), t:r.t, pt:r.pt });
          }
          if(hits.length>=2){                            // crossed windward + leeward → valid cut
            hits.sort((x,y)=>x.t-y.t);
            const sAcross = axis==="v" ? hits[0].pt.x : hits[0].pt.y;  // where the cut meets windward
            setSections(s=>({...s, [axis]:{ axis, sign }}));
            pendingOpen.current = { axis, key:hits[0].key, sAcross };
          }
          // fewer than 2 exterior walls crossed → not a section; do nothing
        }
      }
    }
  },[toUser,thawView,bindNodeToWall,placeDrawPoint]);

  const onLeave = useCallback(e=>{ onUp(e); },[onUp]);

  const onDimClick = useCallback((edge,e)=>{
    e.stopPropagation();
    if(panModeRef.current) return;                          // pan tool active → don't open dim editor
    if(touchTrack(e)) return;                               // (rev 71) 2nd finger → pinch
    if(drawModeRef.current){ drawDown(e); return; }         // draw mode: a tap over a dim label places a node (touch defers to lift)
    const g=graphRef.current;
    const a=g.nodes.find(n=>n.id===edge.a), b=g.nodes.find(n=>n.id===edge.b);
    if(!a||!b) return;
    // LENGTHEN semantics: the end nearest the click is the one that moves; when the click is
    // ambiguous (near the middle), anchor the better-connected end so the plan stays put.
    const u=toUser(e);
    const L2=(b.x-a.x)**2+(b.y-a.y)**2 || 1;
    const t=((u.x-a.x)*(b.x-a.x)+(u.y-a.y)*(b.y-a.y))/L2;     // 0 at a, 1 at b
    let moveEnd;
    if(Math.abs(t-0.5) >= 0.10) moveEnd = t<0.5 ? "a" : "b";
    else{
      const deg=(id)=>g.edges.reduce((c,ed)=>c+(ed.a===id||ed.b===id?1:0),0);
      moveEnd = deg(edge.a) <= deg(edge.b) ? "a" : "b";       // move the less-connected end
    }
    const r=stageRef.current.getBoundingClientRect();
    const m=svgRef.current.getScreenCTM();
    const mx=(a.x+b.x)/2, my=(a.y+b.y)/2;
    const sx=m.a*mx+m.c*my+m.e, sy=m.b*mx+m.d*my+m.f;
    setDimEdit({edge, moveEnd, px:sx-r.left, py:sy-r.top-18, val:String(fmtHalf(dist(a,b)))});
    setMenu(null);
  },[toUser,placeDrawPoint,touchTrack,drawDown]);

  // ── DERIVED ──
  const loop = useMemo(()=>loopInfo(graph.nodes,graph.edges),[graph]);
  const totalLen = useMemo(()=>graph.edges.reduce((s,e)=>{
    const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
    return a&&b ? s+dist(a,b) : s;
  },0),[graph]);

  const gridLines=[];
  { const x0=Math.floor(view.x/gridStep)*gridStep, xe=view.x+view.w;
    const y0=Math.floor(view.y/gridStep)*gridStep, ye=view.y+view.h;
    for(let x=x0;x<=xe;x+=gridStep) gridLines.push({x1:x,y1:view.y,x2:x,y2:ye});
    for(let y=y0;y<=ye;y+=gridStep) gridLines.push({x1:view.x,y1:y,x2:xe,y2:y}); }

  const selNode = selected!==null ? graph.nodes.find(n=>n.id===selected) : null;

  // per-orientation section render data + line load
  const isSup = useCallback((key)=>!noSupport.has(key),[noSupport]);
  // (2-story mode) a wall tagged 1-story rises only to the floor diaphragm; it never reaches the roof.
  // Step 1 is the tag + appearance only — the load/floor-view effects land in the following steps.
  const isOneStory = useCallback((key)=> twoStory && oneStory.has(key), [twoStory, oneStory]);
  const propsFor = useCallback((key)=> mergeWallProps(wallProps[key]), [wallProps]);
  // (rev 57) live 1-story seismic effective weight (W_total) from the plan geometry + the relocated
  // Roof DL / Wall DL. Reactive to graph, wall props (par/H), and g.roofDL/g.wallDL.
  const sw = useMemo(()=> seismicWeight1Story(graph, loop, propsFor, g&&g.roofDL, g&&g.wallDL),
                     [graph, loop, propsFor, g]);
  // (rev 60) lift W_total to App for the Design-tab Seismic card: 2-story now has a real per-diaphragm
  // total (sw2), so V = Cs·W shows on both tabs in either mode (was null/"—" in 2-Story before).
  // In 2-story mode the on-plan loads/reactions reflect the SELECTED floor, by feeding buildSecData a
  // floor-specific EFFECTIVE wall height (engine untouched — it reads pr.H only in the line-load term):
  //   2nd-floor plan → roof diaphragm:  H_eff = H₂            → ½·H₂·pw + parapets               (designs 2nd-floor walls)
  //   1st-floor plan → 2nd-floor diaph.: H_eff = H + 2·H₂     → ½·H·pw + H₂·pw + parapets         (designs 1st-floor walls)
  // 1-story mode passes props through unchanged (byte-identical to before).
  const propsForActive = useCallback((key)=>{
    const p = propsFor(key);
    if(!twoStory) return p;
    const H=p.H||0, H2=p.H2||0;
    return { ...p, H: activeFloor===2 ? H2 : H + 2*H2 };
  },[propsFor, twoStory, activeFloor]);
  // rev 34 — 2-story FLOOR-1 ON-PLAN LABEL (display only). The 2nd-floor diaphragm carries ONLY the
  // half-walls above and below it (½·H·pw + ½·H₂·pw); the roof diaphragm + parapets do NOT pour into
  // it — that load transfers down through the 2nd-story shear wall into the 1st-story wall as a POINT
  // load. The combined load above (H+2·H₂ via propsForActive) still drives the REACTIONS/point loads
  // (unchanged), so this floor-only value is purely what the plan LABEL shows. Uniform along a wall
  // (no leeward-parapet term → it cancels), and uses the REAL H/H₂ (not the propsForActive substitution).
  const floorDiaphragmPlf = useCallback((key)=>{
    const p = propsFor(key);
    return 0.5*(p.pw||0)*((p.H||0)+(p.H2||0));
  },[propsFor]);
  // (rev 56) GLOBAL INPUTS — open seeds each field from the building-wide CONSENSUS: if every relevant
  // wall already shares a value, show it; if walls differ (or there are none), fall back to the default.
  // par1/par2 are seeded from walls tagged 1-story / 2-story respectively (in 2-story mode), so reopening
  // reflects what's actually applied.
  const openGlobalInputs = useCallback(()=>{
    const D = DEF_SECTION;
    const keys = graphRef.current.edges.map(keyOf);
    const oneKeys = keys.filter(k=>oneStory.has(k));
    const twoKeys = keys.filter(k=>!oneStory.has(k));
    const cons = (get, ks)=>{                       // common value across ks, else null
      let v=null, first=true;
      for(const k of ks){ const val=get(propsFor(k)); if(first){ v=val; first=false; } else if(val!==v) return null; }
      return first ? null : v;
    };
    setGlobalInputs({
      H:     cons(p=>p.H,     keys)                       ?? D.H,
      H2:    cons(p=>p.H2,    keys)                       ?? D.H,            // H2 default mirrors H
      par1:  cons(p=>p.par,   twoStory ? oneKeys : keys)  ?? D.par,
      par2:  cons(p=>p.par,   twoKeys)                    ?? D.par,
      pw:    cons(p=>p.pw,    keys)                       ?? D.pw,
      qWind: cons(p=>p.qWind, keys)                       ?? D.qWind,
      qLee:  cons(p=>p.qLee,  keys)                       ?? D.qLee,
    });
  },[propsFor, oneStory, twoStory]);
  // Apply the entered values to EVERY wall's props in one setState. 1-story mode leaves H2 untouched
  // (there is no 2nd level); 2-story mode sets H + H2 on all walls and routes the parapet height by the
  // 1-story tag. Spreading the current entry first preserves per-wall DL tributary + any other fields.
  const applyGlobalInputs = useCallback((vals)=>{
    const num = (s)=> Math.max(0, parseFloat(s)||0);
    const H=num(vals.H), H2=num(vals.H2), pw=num(vals.pw), qWind=num(vals.qWind), qLee=num(vals.qLee);
    const par1=num(vals.par1), par2=num(vals.par2);
    setWallProps(prev=>{
      const next={...prev};
      for(const e of graphRef.current.edges){
        const k=keyOf(e);
        const cur = next[k] || DEF_SECTION;
        next[k] = twoStory
          ? { ...cur, H, H2, par:(oneStory.has(k) ? par1 : par2), pw, qWind, qLee }
          : { ...cur, H,      par:par1,                            pw, qWind, qLee };
      }
      return next;
    });
    setGlobalInputs(null);
  },[twoStory, oneStory]);
  const toggleSupport = useCallback((edge)=>{
    const k=keyOf(edge);
    setNoSupport(s=>{ const n=new Set(s); n.has(k)?n.delete(k):n.add(k); return n; });
  },[]);
  const toggleOneStory = useCallback((edge)=>{
    const k=keyOf(edge);
    setOneStory(s=>{ const n=new Set(s); n.has(k)?n.delete(k):n.add(k); return n; });
  },[]);
  // ── STEP 2: 2nd-floor (roof diaphragm) excludes 1-story walls ──
  // A 1-story wall stops at the floor diaphragm, so it does NOT exist on the 2nd-floor (roof) plan.
  // We feed buildSecData a FILTERED graph (full graph minus the 1-story walls + their now-orphaned
  // nodes) for the 2nd-floor view. This drops 1-story walls from windward collection, the overlap-
  // shadow test, AND lineReactions supports in ONE move — the guarded engine is untouched, it just
  // receives a smaller graph. The full graph still RENDERS every wall (green ones drawn, load-less).
  // Zeroing via propsFor would NOT work: a 1-story wall geometrically in front of the box would
  // wrongly shadow it — removing the wall from the graph is the correct fix.
  const twoStoryGraph = useMemo(()=>{
    if(!twoStory || oneStory.size===0) return graph;
    const keepE = graph.edges.filter(e=>!oneStory.has(keyOf(e)));
    const used = new Set(); keepE.forEach(e=>{ used.add(e.a); used.add(e.b); });
    return { nodes: graph.nodes.filter(n=>used.has(n.id)), edges: keepE };
  },[twoStory, oneStory, graph]);
  const twoStoryLoop = useMemo(()=>loopInfo(twoStoryGraph.nodes, twoStoryGraph.edges),[twoStoryGraph]);
  // 2nd-floor (roof) → filtered graph; 1st-floor + 1-story mode → full graph (unchanged).
  const roofView = twoStory && activeFloor===2;
  // STEP 3: 1st-floor view with ≥1 tagged 1-story wall → the mixed-height accumulation builder.
  const mixed1 = twoStory && activeFloor===1 && oneStory.size>0;
  const secGraph = roofView ? twoStoryGraph : graph;
  const secLoop  = roofView ? twoStoryLoop : loop;
  const secH = useMemo(()=> mixed1
        ? buildSecDataF1(sections.h, graph, loop, isSup, propsFor, isOneStory)
        : buildSecData(sections.h, secGraph, secLoop, isSup, propsForActive),
      [mixed1,sections.h,graph,loop,secGraph,secLoop,isSup,propsFor,propsForActive,isOneStory]);
  const secV = useMemo(()=> mixed1
        ? buildSecDataF1(sections.v, graph, loop, isSup, propsFor, isOneStory)
        : buildSecData(sections.v, secGraph, secLoop, isSup, propsForActive),
      [mixed1,sections.v,graph,loop,secGraph,secLoop,isSup,propsFor,propsForActive,isOneStory]);
  // (2-story mode) warn when EVERY wall has been tagged 1-story — then the 2nd floor has no walls.
  const allOneStory = useMemo(()=> twoStory && graph.edges.length>0
        && graph.edges.every(e=>oneStory.has(keyOf(e))), [twoStory, graph.edges, oneStory]);
  // SEISMIC distribution.  A diaphragm force F is spread as a uniform line load along the boundary
  // faces perpendicular to each direction: w = F / (projected extent ⟂ the force). Force X (axis "h")
  // → extent = Y-span (D), loads the Y-running faces; Force Y (axis "v") → extent = X-span (B), loads
  // the X-running faces. Reuses the generalized buildSecData (Option B) with a uniform load model
  // { base:()=>w, lee:()=>0 }, so the windward-collection + across-wind shadow + lineReactions geometry
  // distributes F (conserving it — the shadow filter keeps a face set whose transverse projections
  // tile the extent once) and yields wall reactions exactly like wind.
  //   1-story (rev 59): one diaphragm, F = V = Cs·W_total.
  //   2-story (rev 60): per-level weights → vertical distribution F_roof / F_floor (Phase 3), then the
  //     ACTIVE-floor force is distributed: roof view (level 2) on the 2-story-only walls (twoStoryGraph,
  //     the roof exists only there), floor view (level 1) on the full graph.
  const Cs = Number(g&&g.Cs)||0;
  const sw2 = useMemo(()=> twoStory
        ? seismicWeight2Story(graph, loop, twoStoryLoop, propsFor, isOneStory, g&&g.roofDL, g&&g.floorDL, g&&g.wallDL)
        : null, [twoStory, graph, loop, twoStoryLoop, propsFor, isOneStory, g]);
  const seis2 = useMemo(()=> seismicDistribute2Story(sw2, Cs), [sw2, Cs]);
  useEffect(()=>{ if(setWtotal) setWtotal(twoStory ? (sw2?sw2.Wtotal:null) : sw.Wtotal); },
    [twoStory, sw.Wtotal, sw2, setWtotal]);
  // the diaphragm force to distribute on the CURRENT plan view
  const Vview = twoStory ? (seis2 ? (activeFloor===2 ? seis2.Froof : seis2.Ffloor) : 0)
                         : Cs*sw.Wtotal;
  // the graph/loop the seismic diaphragm spans on this view (roof = 2-story walls only)
  const seisGraph = (twoStory && activeFloor===2) ? twoStoryGraph : graph;
  const seisLoop  = (twoStory && activeFloor===2) ? twoStoryLoop  : loop;
  const bbox = (ns)=>{ if(!ns.length) return {dx:0,dy:0};
    let mnX=Infinity,mnY=Infinity,mxX=-Infinity,mxY=-Infinity;
    ns.forEach(p=>{mnX=Math.min(mnX,p.x);mnY=Math.min(mnY,p.y);mxX=Math.max(mxX,p.x);mxY=Math.max(mxY,p.y);});
    return { dx:mxX-mnX, dy:mxY-mnY }; };
  const seisExtent     = useMemo(()=> bbox(graph.nodes),      [graph.nodes]);      // full-plan bbox (1-story card)
  const twoStoryExtent = useMemo(()=> bbox(twoStoryGraph.nodes), [twoStoryGraph]); // (rev 63) 2-story sub-plan bbox — F_roof spans only this
  const seisViewExtent = useMemo(()=> bbox(seisGraph.nodes),  [seisGraph]);        // bbox of the diaphragm being drawn
  const wSeisX = seisViewExtent.dy>0 ? Vview/seisViewExtent.dy : 0;   // force-X plf (on the Y-running faces)
  const wSeisY = seisViewExtent.dx>0 ? Vview/seisViewExtent.dx : 0;   // force-Y plf (on the X-running faces)
  const seisOn = loadCase==="seismic" && Vview>0 && !!seisLoop;
  const seisModelH = useMemo(()=>({ base:()=>wSeisX, lee:()=>0 }),[wSeisX]);
  const seisModelV = useMemo(()=>({ base:()=>wSeisY, lee:()=>0 }),[wSeisY]);
  const secSeisH = useMemo(()=> seisOn ? buildSecData({axis:"h",sign:-1}, seisGraph, seisLoop, isSup, propsFor, seisModelH) : null,
        [seisOn, seisGraph, seisLoop, isSup, propsFor, seisModelH]);
  const secSeisV = useMemo(()=> seisOn ? buildSecData({axis:"v",sign:-1}, seisGraph, seisLoop, isSup, propsFor, seisModelV) : null,
        [seisOn, seisGraph, seisLoop, isSup, propsFor, seisModelV]);
  // what the canvas draws: wind sections, or the seismic ones when the Load-case toggle is on Seismic
  const showSeis = loadCase==="seismic";
  const dispH = showSeis ? secSeisH : secH;
  const dispV = showSeis ? secSeisV : secV;
  useEffect(()=>{
    const po=pendingOpen.current; if(!po) return; pendingOpen.current=null;
    const ax=po.axis; const sc=ax==="h"?secH:secV;
    const sign = sectionsRef.current[ax] && sectionsRef.current[ax].sign;
    // The section is an OVERALL-BUILDING cut: anchor its windward wall to the FULL graph at the cut
    // position, so the SAME section shows on the 1st-floor and 2nd-floor plans (rev 40). Before, the
    // 2nd-floor view's filtered windLoads dropped the 1-story windward wall → a different section.
    const seq = sectionSequence(po.sAcross, ax, sign, graphRef.current, propsFor, isOneStory);
    let key = po.key;
    if((!key || !seq.some(w=>w.key===key)) && seq.length) key = seq[0].key;   // true windward wall
    if(!key && sc && sc.windLoads.length) key = sc.windLoads[0].key;          // last-resort fallback
    if(key) setActiveWall({axis:ax, key, sAcross:po.sAcross});
  },[secH,secV]);

  // The active windward wall's leeward (back) partner — resolves the specific back segment behind
  // this cut, so the leeward parapet shown is that wall's own height (shared when the back is one
  // wall, distinct when it's split).
  const activeLeeKey = useMemo(()=> activeWall
      ? findLeewardPartner(activeWall.key, activeWall.axis, sections[activeWall.axis]&&sections[activeWall.axis].sign, graph, activeWall.sAcross)
      : null,
    [activeWall, sections, graph]);

  const activeSection = activeWall ? (()=>{
    const self = propsFor(activeWall.key);
    const lee  = activeLeeKey ? propsFor(activeLeeKey) : null;
    const sign = sections[activeWall.axis]&&sections[activeWall.axis].sign;
    // (rev 39) for a 1-story cut wall, the nearest 2-story portion DOWNWIND of it (the box) → drives
    // the stepped section drawing + the ½·H₂·pw accumulation shown in the window.
    const behind = isOneStory(activeWall.key)
      ? nearestTwoStoryBehind(activeWall.key, activeWall.axis, sign, graph, propsFor, (k)=>oneStory.has(k))
      : null;
    // (rev 40) the full ordered run of walls this overall-building cut crosses → drives SecDiagramSeq
    // + the section type (A/B/C/C-rev). Floor-independent (always the full graph at the cut position).
    const sAt = activeWall.sAcross!=null ? activeWall.sAcross
              : (()=>{ const e=graph.edges.find(x=>keyOf(x)===activeWall.key); if(!e) return null;
                       const a=graph.nodes.find(n=>n.id===e.a), b=graph.nodes.find(n=>n.id===e.b);
                       return a&&b ? (activeWall.axis==="v"?(a.x+b.x)/2:(a.y+b.y)/2) : null; })();
    const seq = sectionSequence(sAt, activeWall.axis, sign, graph, propsFor, isOneStory);
    return { H:self.H, pw:self.pw, qWind:self.qWind, qLee:self.qLee,
             par:self.par,                       // windward parapet = this wall's own
             H2:self.H2,                          // 2nd-story wall height (resolves to H when unset)
             leePar: lee ? lee.par : 0,          // leeward parapet  = back wall's own
             leeH:  lee ? lee.H   : 0,           // leeward wall height = back wall's own H (sloping roof)
             leeH2: lee ? lee.H2  : 0,           // leeward 2nd-story height = back wall's own H2 (2-story)
             behind,                              // {H2,pw,par,…} of the nearest 2-story wall behind, or null
             seq,                                 // ordered walls front→back (overall-building section)
             axis:activeWall.axis,
             sign };
  })() : null;

  // Build one shear-wall design line per point-load support wall and hand off to the Design tab:
  // full collinear extent (even when the support is split), max wall height H along it, and the
  // reaction kips it carries. Parapets are irrelevant to the shear-wall calc and are not sent.
  // rev 130 — STALE-PUSH INDICATOR (Plan→Design). `pushedSig` = the handoff signature
  // captured the last time the user pressed "Design shear walls". It is null until a push
  // (so the button is only ever red AFTER a push, per spec) and is reset on New/Open below.
  const [pushedSig, setPushedSig] = useState(null);
  // `computeHandoff` is the OLD runDesignHandoff body with NO side effect — it just returns
  // `byFloor`. The actual push (runDesignHandoff) calls it then hands off; the live signature
  // memo calls it on every relevant plan change to detect divergence. (Not a guarded engine fn.)
  const computeHandoff = useCallback(()=>{
    // rev 62/63: per-line SEISMIC reaction, computed UNCONDITIONALLY (independent of the Wind/Seismic
    // view toggle + active floor) so each design line carries its own seismic demand while the canvas
    // shows wind. vSeismic is the post-R reduced base shear (rev 61), fed straight to the engine.
    //   1-story: one map — V = Cs·W_total distributed on the full plan (rev-59 mechanism).
    //   2-story (rev 63): per-floor — F_roof on the 2-story sub-plan (the roof exists only on 2-story
    //     walls), F_floor on the full plan, using the rev-60 vertical distribution seis2.Froof/Ffloor.
    // The per-floor force is read in buildFloor and joined by axis|key (same key as the wind reaction).
    const seisMapFor = (F, fGraph, fLoop, ext) => {
      const m = {}; if(!(F>0) || !fLoop) return m;
      const wX = ext.dy>0 ? F/ext.dy : 0;   // force-X plf on the Y-running faces
      const wY = ext.dx>0 ? F/ext.dx : 0;   // force-Y plf on the X-running faces
      const sH = buildSecData({axis:"h",sign:-1}, fGraph, fLoop, isSup, propsFor, { base:()=>wX, lee:()=>0 });
      const sV = buildSecData({axis:"v",sign:-1}, fGraph, fLoop, isSup, propsFor, { base:()=>wY, lee:()=>0 });
      (sH ? sH.reactions : []).forEach(rr=>{ if(rr.kips>0) m["h|"+rr.key]=rr.kips*1000; });
      (sV ? sV.reactions : []).forEach(rr=>{ if(rr.kips>0) m["v|"+rr.key]=rr.kips*1000; });
      return m;
    };
    const Cs = Number(g&&g.Cs)||0;
    const seisMap1 = !twoStory                                       // floor-1 (or the only floor)
          ? seisMapFor(Cs*(sw?sw.Wtotal:0), graph, loop, seisExtent)
          : seisMapFor(seis2?seis2.Ffloor:0, graph, loop, seisExtent);
    const seisMap2 = twoStory                                        // floor-2 (roof) — 2-story sub-plan only
          ? seisMapFor(seis2?seis2.Froof:0, twoStoryGraph, twoStoryLoop, twoStoryExtent)
          : {};
    // Build the design lines for ONE floor: re-run the frozen wind engine with that floor's effective
    // wall height (same substitution as propsForActive), and tag each line with the floor's DESIGN
    // height (floor 2 walls are H₂ tall, floor 1 walls are H tall) and its reaction.
    const buildFloor=(floor)=>{
      const seisMap = (twoStory && floor===2) ? seisMap2 : seisMap1;   // rev 63: floor-2 → roof force map, else floor-1/1-story map
      const fg = (twoStory && floor===2) ? twoStoryGraph : graph;   // step 2: roof floor excludes 1-story walls
      const fl = (twoStory && floor===2) ? twoStoryLoop  : loop;
      const mixedF1 = twoStory && floor===1 && oneStory.size>0;       // step 3: mixed-height 1st-floor accumulation
      const pf=(key)=>{ const p=propsFor(key); if(!twoStory) return p; const H=p.H||0,H2=p.H2||0; return {...p, H: floor===2 ? H2 : H+2*H2}; };
      const scH = mixedF1 ? buildSecDataF1(sections.h, fg, fl, isSup, propsFor, isOneStory) : buildSecData(sections.h, fg, fl, isSup, pf);
      const scV = mixedF1 ? buildSecDataF1(sections.v, fg, fl, isSup, propsFor, isOneStory) : buildSecData(sections.v, fg, fl, isSup, pf);
      const lines=[];
      [["h",scH],["v",scV]].forEach(([ax,sc])=>{
        if(!sc) return;
        sc.reactions.forEach(r=>{
          if(!(r.kips>0)) return;
          const e=fg.edges.find(x=>keyOf(x)===r.key); if(!e) return;
          const ea=fg.nodes.find(n=>n.id===e.a), eb=fg.nodes.find(n=>n.id===e.b); if(!ea||!eb) return;
          const o=edgeAxis(ea,eb);
          const fixed = o==="h" ? ea.y : ea.x;
          let lo=Infinity, hi=-Infinity, Hmax=0; const ivals=[];
          fg.edges.forEach(e2=>{
            if(!isSup(keyOf(e2))) return;
            const a2=fg.nodes.find(n=>n.id===e2.a), b2=fg.nodes.find(n=>n.id===e2.b); if(!a2||!b2) return;
            if(edgeAxis(a2,b2)!==o) return;
            const f2 = o==="h" ? (a2.y+b2.y)/2 : (a2.x+b2.x)/2;
            if(Math.abs(f2-fixed)>0.75) return;
            const v0 = o==="h" ? Math.min(a2.x,b2.x) : Math.min(a2.y,b2.y);
            const v1 = o==="h" ? Math.max(a2.x,b2.x) : Math.max(a2.y,b2.y);
            lo=Math.min(lo,v0); hi=Math.max(hi,v1); ivals.push([v0,v1]);   // (rev 73) record each solid wall span
            const pp=propsFor(keyOf(e2));
            Hmax=Math.max(Hmax, (twoStory && floor===2 ? (pp.H2||0) : (pp.H||0)));   // design height per floor
          });
          if(!(hi>lo)) return;
          // (rev 73) merge the collinear support edges into SOLID RUNS in line-local coords (0 = the `a`
          // end), so the Design tab can snap a shear-wall segment INTO a real wall instead of a gap
          // (an opening between two collinear walls). Display/placement only — never read by the engine.
          ivals.sort((p,q)=>p[0]-q[0]);
          const runs=[];
          ivals.forEach(([s,e])=>{ const last=runs[runs.length-1];
            if(last && s <= last[1] + 1e-6) last[1]=Math.max(last[1], e);
            else runs.push([s, e]); });
          const runsLocal = runs.map(([s,e])=>[+(s-lo).toFixed(4), +(e-lo).toFixed(4)]);
          const a = o==="h" ? {x:lo,y:fixed} : {x:fixed,y:lo};
          const b = o==="h" ? {x:hi,y:fixed} : {x:fixed,y:hi};
          // (rev 49) carry this line's DEAD-LOAD tributary from the keyed support wall, picking the
          // floor-appropriate pair so a stacked wall can use a different trib on each floor. The rev-48
          // geometric pairing below spreads ...l, so a 1st-floor line keeps ITS trib after adopting the
          // 2nd floor's geometry. ?? falls back to the base pair for any wall missing the 2nd-floor keys.
          const wp = propsFor(r.key);
          const f2 = twoStory && floor===2;
          const roofTrib  = f2 ? (wp.roofTrib2  ?? wp.roofTrib)  : wp.roofTrib;
          const floorTrib = f2 ? (wp.floorTrib2 ?? wp.floorTrib) : wp.floorTrib;
          lines.push({ id:ax+"|"+r.key, key:r.key, windAxis:ax, o, a, b,
                       lengthFt:hi-lo, heightFt:Hmax||13, forceLbs:r.kips*1000,
                       forceLbsSeismic: seisMap[ax+"|"+r.key] || 0,   // rev 62/63: per-line seismic demand (1-story, or per-floor for 2-story)
                       roofTrib, floorTrib, runs:runsLocal });        // rev 73: solid wall runs (line-local) for default-placement snapping
        });
      });
      return lines;
    };
    const floors = twoStory ? [2,1] : [1];          // 2nd floor (roof load) + 1st floor (2nd-floor load)
    const byFloor={}; floors.forEach(f=> byFloor[f]=buildFloor(f));
    // STACK ALIGNMENT (rev 47 → rev 48): a stacked wall's 1st-floor line spans the FULL wall (built on
    // the full graph) while its 2nd-floor line spans only the 2-story sub-segment (twoStoryGraph). They
    // do NOT necessarily share an id: the collinear-support cluster (see ~line 201) keys each line to
    // its LONGEST collinear edge, which for the 1st floor is often the 1-STORY portion — so id-based
    // pairing (rev 47) missed them and left TWO independent lines. Result the user saw: the two floors'
    // shear walls didn't share a segment array (length/position edits on one floor didn't reach the
    // other) and centered in different spans (the wall "shifted" on a floor switch). Pair them
    // GEOMETRICALLY instead — each 2nd-floor line adopts the collinear 1st-floor line that contains it
    // (same orientation + wind axis + fixed coordinate; tightest span that covers the 2-story segment)
    // — then that 1st-floor line takes the 2nd floor's id + extent (a/b/lengthFt) while KEEPING its own
    // 1st-floor reaction + design height. Both floors then share ONE id (→ one segsByLine entry, so they
    // move + stretch together) and ONE geometry (→ aligned, centered identically, confined to the 2-story
    // segment). Uniform 2-story walls already coincide → pairing is an identity; 1-story-only lines find
    // no 2-story partner and are left untouched.
    if(twoStory && byFloor[1] && byFloor[2]){
      const fixedOf=(l)=> l.o==="h" ? l.a.y : l.a.x;
      const spanOf =(l)=> l.o==="h" ? [Math.min(l.a.x,l.b.x),Math.max(l.a.x,l.b.x)]
                                    : [Math.min(l.a.y,l.b.y),Math.max(l.a.y,l.b.y)];
      const claimed=new Set(), paired=new Map();
      byFloor[2].forEach(u=>{
        const [ulo,uhi]=spanOf(u);
        let best=null, bestScore=-Infinity;
        byFloor[1].forEach(l=>{
          if(claimed.has(l) || l.o!==u.o || l.windAxis!==u.windAxis) return;
          if(Math.abs(fixedOf(l)-fixedOf(u))>0.75) return;
          const [llo,lhi]=spanOf(l);
          const overlap=Math.min(lhi,uhi)-Math.max(llo,ulo);
          if(overlap<=0.5) return;
          const contains = llo<=ulo+0.5 && lhi>=uhi-0.5;
          const score=(contains?1e6:0) + overlap - l.lengthFt*0.001;   // prefer a containing, tightest line
          if(score>bestScore){ best=l; bestScore=score; }
        });
        if(best){ claimed.add(best); paired.set(best,u); }
      });
      byFloor[1]=byFloor[1].map(l=>{ const u=paired.get(l);
        return u ? { ...l, id:u.id, key:u.key, a:u.a, b:u.b, lengthFt:u.lengthFt } : l; });
    }
    return byFloor;
  },[sections, graph, loop, isSup, propsFor, twoStory, twoStoryGraph, twoStoryLoop, oneStory, isOneStory, g, sw, seisExtent, seis2, twoStoryExtent]);

  // Live signature of what a push WOULD send right now. Recomputes whenever any handoff input
  // changes (computeHandoff's identity changes with its deps). Pure-view edits (zoom, markup
  // scale, selection, snap/ortho/dims) are NOT in computeHandoff's deps, so they never trip it.
  const liveHandoffSig = useMemo(()=> JSON.stringify(computeHandoff()), [computeHandoff]);
  // RED when: we have pushed at least once AND re-pushing would change the Design tab's lines.
  const designStaleHint = pushedSig !== null && liveHandoffSig !== pushedSig;
  // The actual push: build the lines, hand them to the Design tab, and snapshot the signature
  // so the button returns to normal until the next upstream edit that would change the result.
  const runDesignHandoff = useCallback(()=>{
    if(!onDesignShearWalls) return;
    const byFloor = computeHandoff();
    onDesignShearWalls(byFloor, {nodes:graph.nodes.map(n=>({...n})), edges:graph.edges.map(e=>({...e}))});
    setPushedSig(JSON.stringify(byFloor));
  },[onDesignShearWalls, computeHandoff, graph]);

  return (
    <div className="r">
      <style>{CSS}</style>

      <div className="hd">
        <h1 className="htitle">Plan Sketcher</h1>
        <span className="htag">
          Left-drag nodes &amp; walls · Drag across empty space to cut a section · Right-click for actions
        </span>
      </div>

      {/* ── COMMAND BAR (mini-ribbon, pinned below the suite tab bar) ──
          Draft toggles (Draw/Snap/Ortho/Dims) live here ONLY; Presets live in the side panel ONLY.
          File (New/Open/Save) moved to the persistent app-level toolbar (rev 69) — accessible from every tab. ── */}
      <div className="ribbon">
        <div className="rgroup">
          <div className="rlabel">Edit</div>
          <div className="rbtns">
            {/* Undo/Redo promoted to the app-level file toolbar (rev 70); Clear stays (plan-specific). */}
            <button className="rbtn" title="Clear the plan" onClick={clearAll}>🗑 Clear</button>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Inputs</div>
          <div className="rbtns">
            <button className="rbtn"
              disabled={graph.edges.length===0}
              title={graph.edges.length===0 ? "Draw at least one wall first" : "Apply wall/parapet heights and pressures to the whole building"}
              onClick={openGlobalInputs}>⚙ Global inputs…</button>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Draft</div>
          <div className="rbtns">
            <button className={"rbtn"+(drawMode?" ron":"")} title="Draw walls — click to chain segments" onClick={toggleDrawMode}>✏ Draw</button>
            <button className={"rbtn"+(snapOn?" ron":"")} title="Snap to grid" onClick={()=>setSnapOn(v=>!v)}>⌗ Snap</button>
            <button className={"rbtn"+(ortho?" ron":"")} title="Orthogonal (90°)" onClick={()=>setOrtho(v=>!v)}>∟ Ortho</button>
            <button className={"rbtn"+(dims?" ron":"")} title="Show dimensions" onClick={()=>setDims(v=>!v)}>⟷ Dims</button>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">View</div>
          <div className="rbtns">
            <button className="rbtn" title="Zoom to fit the whole plan (resets manual zoom)" onClick={zoomToFit}>⊡ Fit</button>
            <button className="rbtn" title="Zoom in" onClick={()=>{ const r=svgRef.current?.getBoundingClientRect(); if(r) zoomAt(r.left+r.width/2, r.top+r.height/2, 1/1.25); }}>+ In</button>
            <button className="rbtn" title="Zoom out — or scroll the mouse wheel over the canvas; middle-drag to pan" onClick={()=>{ const r=svgRef.current?.getBoundingClientRect(); if(r) zoomAt(r.left+r.width/2, r.top+r.height/2, 1.25); }}>− Out</button>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Markup</div>
          <div className="rbtns">
            <select className="rsel" title="On-plan markup scale — shrink the labels, the load/reaction arrows, AND the nodes together so the markup doesn't cover a zoomed-out plan"
                    value={markScale} onChange={e=>setMarkScale(parseFloat(e.target.value))}>
              <option value="1">1×</option>
              <option value="0.75">0.75×</option>
              <option value="0.5">0.5×</option>
              <option value="0.25">0.25×</option>
            </select>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Stories</div>
          <div className="rbtns">
            <div className={"storypill"+(twoStory?" two":"")}
                 title="Switch between single-story and two-story design">
              <span className="storythumb"/>
              <button className={"storyopt"+(!twoStory?" on":"")} onClick={()=>setTwoStory(false)}>1 Story</button>
              <button className={"storyopt"+(twoStory?" on":"")} onClick={()=>setTwoStory(true)}>2 Story</button>
            </div>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Load case</div>
          <div className="rbtns">
            <div className={"storypill"+(loadCase==="seismic"?" two":"")}
                 title="Show wind loads or the seismic base-shear loads on the plan">
              <span className="storythumb"/>
              <button className={"storyopt"+(loadCase==="wind"?" on":"")} onClick={()=>setLoadCase("wind")}>Wind</button>
              <button className={"storyopt"+(loadCase==="seismic"?" on":"")} onClick={()=>setLoadCase("seismic")}>Seismic</button>
            </div>
          </div>
        </div>
        <div className="rsep"/>
        <div className="rgroup">
          <div className="rlabel">Analyze</div>
          <div className="rbtns">
            <button className="rbtn rprimary"
              title={designStaleHint ? "Plan changed since you last sent it — click to update the Design tab" : "Send point-load walls to the shear-wall designer"}
              disabled={!((secH&&secH.reactions.length)||(secV&&secV.reactions.length))}
              style={(designStaleHint && ((secH&&secH.reactions.length)||(secV&&secV.reactions.length))) ? STALE_BTN : undefined}
              onClick={runDesignHandoff}>
              {designStaleHint && WARN}⚡ Design shear walls
            </button>
          </div>
        </div>
      </div>

      <div className="layout">
        <div className="canvascol">
        {/* ── PLAN SELECTOR — directly ABOVE the drawing area (outside the canvas, so clicks never hit the SVG). Greyed/disabled until 2-Story is on. ── */}
        <div className={"floorbar"+(twoStory?"":" off")}>
          <div className="floorsel"
               title={twoStory?"Choose which plan to view":"Turn on 2 Story (top toolbar) to enable plan switching"}>
            <button className={"floortab"+(activeFloor===1?" act":"")} disabled={!twoStory}
                    onClick={()=>twoStory&&setActiveFloor(1)}>Level 1</button>
            <button className={"floortab"+(activeFloor===2?" act":"")} disabled={!twoStory}
                    onClick={()=>twoStory&&setActiveFloor(2)}>Level 2</button>
          </div>
        </div>
        <div className="stage" ref={stageRef}>
          {twoStory && (<div className="floorbadge">Level {activeFloor} <span>Plan</span></div>)}
          {healNote!=null && (<div className="healtoast" onClick={()=>setHealNote(null)} title="Click to dismiss">
            ✓ Repaired {healNote} stray edge{healNote===1?"":"s"} on load <span>— the plan boundary is now consistent</span>
          </div>)}
          {allOneStory && (<div className="allonestory-warn">⚠ All walls are 1-story — the 2nd floor has no walls.</div>)}
          <svg ref={svgRef} className="cvs" style={drawMode?{cursor:"crosshair"}:(panMode||panCursor)?{cursor:panCursor?"grabbing":"grab"}:undefined}
               viewBox={`${view.x} ${view.y} ${view.w} ${view.h}`}
               onPointerDown={onBgLDown} onPointerMove={onMove} onPointerUp={onUp}
               onPointerLeave={onLeave} onContextMenu={onBgContextMenu}>
            <defs>
              <marker id="loadArr" markerWidth="6" markerHeight="6" refX="4.6" refY="3" orient="auto">
                <path d="M0,0 L6,3 L0,6 Z" fill={C_LOAD}/>
              </marker>
              <marker id="reactArr" markerWidth="6.5" markerHeight="6.5" refX="5" refY="3.25" orient="auto">
                <path d="M0,0 L6.5,3.25 L0,6.5 Z" fill={C_REACT}/>
              </marker>
            </defs>

            <rect x={view.x} y={view.y} width={view.w} height={view.h} fill={C_BG}/>
            {gridLines.map((l,i)=>(<line key={i} {...l} stroke={C_GRID} strokeWidth={0.2*S} opacity=".55"/>))}

            {/* walls */}
            {graph.edges.map(ed=>{
              const a=graph.nodes.find(n=>n.id===ed.a), b=graph.nodes.find(n=>n.id===ed.b);
              if(!a||!b) return null;
              const L=dist(a,b), mx=(a.x+b.x)/2, my=(a.y+b.y)/2;
              const editing=dimEdit&&same(dimEdit.edge,ed);
              const noPL=!isSup(keyOf(ed));
              const oneSty=isOneStory(keyOf(ed));   // (2-story mode) 1-story-only wall → green
              return(
                <g key={`e${ed.a}-${ed.b}`}>
                  <line x1={a.x} y1={a.y} x2={b.x} y2={b.y} stroke={oneSty?C_ONESTORY:C_WALL} strokeWidth={0.55*S} strokeLinecap="round"
                        strokeDasharray={noPL?`${1.6*S} ${1.4*S}`:undefined} opacity={noPL?0.55:1}/>
                  <line x1={a.x} y1={a.y} x2={b.x} y2={b.y} stroke="transparent" strokeWidth={4*S} style={{cursor:"grab"}}
                        onPointerDown={e=>onWallLDown(ed,e)} onContextMenu={e=>openMenu(e,{kind:"wall",edge:ed})}/>
                </g>
              );
            })}

            {/* draw-mode rubber band: anchor → preview, edge-pinned length, ghost node, distinct snap cue */}
            {drawMode && drawPrev && (()=>{
              const anchor = drawAnchor!==null ? graph.nodes.find(n=>n.id===drawAnchor) : null;
              const r = 1.4*S;
              return (
                <g pointerEvents="none">
                  {anchor && <line x1={anchor.x} y1={anchor.y} x2={drawPrev.x} y2={drawPrev.y}
                                   stroke={C_WALL} strokeWidth={0.45*S} strokeDasharray={`${1.6*S} ${1.2*S}`} opacity="0.85"/>}
                  {/* (rev 71) length label is CLAMPED into the visible view (minus a margin) so a long
                      line's midpoint can't scroll the dimension off-screen — it slides to the edge. */}
                  {anchor && (()=>{ const L=dist(anchor,drawPrev); if(L<0.5) return null;
                    const mx=(anchor.x+drawPrev.x)/2, my=(anchor.y+drawPrev.y)/2;
                    const vert=Math.abs(drawPrev.y-anchor.y)>Math.abs(drawPrev.x-anchor.x);
                    const lp=clampPtToView({x:mx, y:my-1.6*S}, view, Math.max(view.w,view.h)*0.05);
                    return <text x={lp.x} y={lp.y} textAnchor="middle" fontSize={1.35*S*markScale} fontWeight="700"
                                 fill={C_NODE} fontFamily="ui-monospace,Menlo,monospace"
                                 transform={vert?`rotate(-90,${lp.x},${lp.y})`:undefined}>{fmt1(L)}′</text>; })()}
                  {/* (rev 71) DISTINCT SNAP CUE — node-snap = blue square (endpoint), wall-snap = gold X
                      (point on a wall body, will auto-split), free point = the ghost node it'll place. */}
                  {drawPrev.node
                    ? <g>
                        <rect x={drawPrev.x-r} y={drawPrev.y-r} width={2*r} height={2*r} fill="none" stroke={C_NODE} strokeWidth={0.34*S}/>
                        <circle cx={drawPrev.x} cy={drawPrev.y} r={0.4*S} fill={C_NODE}/>
                      </g>
                    : drawPrev.splitEdge
                    ? <g stroke={C_DRAFT} strokeWidth={0.34*S} strokeLinecap="round">
                        <circle cx={drawPrev.x} cy={drawPrev.y} r={r} fill="none" strokeWidth={0.26*S}/>
                        <line x1={drawPrev.x-r*0.7} y1={drawPrev.y-r*0.7} x2={drawPrev.x+r*0.7} y2={drawPrev.y+r*0.7}/>
                        <line x1={drawPrev.x-r*0.7} y1={drawPrev.y+r*0.7} x2={drawPrev.x+r*0.7} y2={drawPrev.y-r*0.7}/>
                      </g>
                    : <circle cx={drawPrev.x} cy={drawPrev.y} r={0.8*S*markScale} fill={C_NODE} opacity="0.55"/>}{/* rev 32: ghost preview matches the (scaled) placed node */}
                </g>
              );
            })()}

            {/* live draft cut */}
            {draft&&(<line x1={draft.x1} y1={draft.y1} x2={draft.x2} y2={draft.y2} stroke={C_DRAFT} strokeWidth={0.5*S} strokeDasharray={`${2*S} ${1.5*S}`} opacity=".7"/>)}

            {/* dashed tributary divides — where the line load changes (front node or projected
                back-wall node) — drawn from the windward face across to the leeward face.
                rev 34: hidden in 2-story FLOOR-1 view — the floor diaphragm load is uniform along
                each wall there (the parapet/leeward variation lives in the ROOF diaphragm only). */}
            {!(twoStory&&activeFloor===1&&!mixed1) && [secH,secV].filter(Boolean).flatMap(sc=>(sc.divides||[]).map((d,i)=>(
              <line key={(sc.axis)+"div"+i} x1={d.x1} y1={d.y1} x2={d.x2} y2={d.y2}
                    stroke={C_LOAD} strokeWidth={0.18*S} strokeDasharray={`${1.4*S} ${1.4*S}`} opacity=".55"/>
            )))}

            {/* windward line-load graphics — one per windward wall (all legs). rev 34: in 2-story
                FLOOR-1 view the label shows the FLOOR-only diaphragm plf (½·H·pw + ½·H₂·pw); the roof
                load reaches the 1st floor through the shear walls as a point load, not the diaphragm. */}
            {dispH&&dispH.windLoads.map((wl,i)=><WindLoad key={(showSeis?"shL":"hL")+wl.key} load={wl} S={S} ts={markScale}
                 prec={showSeis?2:1}
                 displayPlf={!showSeis && twoStory&&activeFloor===1&&!mixed1 ? floorDiaphragmPlf(wl.key) : null}
                 onOpen={showSeis ? undefined : ()=>setActiveWall({axis:"h",key:wl.key})}/>)}
            {dispV&&dispV.windLoads.map((wl,i)=><WindLoad key={(showSeis?"svL":"vL")+wl.key} load={wl} S={S} ts={markScale}
                 prec={showSeis?2:1}
                 displayPlf={!showSeis && twoStory&&activeFloor===1&&!mixed1 ? floorDiaphragmPlf(wl.key) : null}
                 onOpen={showSeis ? undefined : ()=>setActiveWall({axis:"v",key:wl.key})}/>)}

            {/* aggregated reactions (a shared support wall sums contributions into one arrow) */}
            {dispH&&dispH.reactions.map((r,i)=><Reaction key={(showSeis?"shR":"hR")+i} r={r} tdir={dispH.tdir} S={S} ts={markScale}/>)}
            {dispV&&dispV.reactions.map((r,i)=><Reaction key={(showSeis?"svR":"vR")+i} r={r} tdir={dispV.tdir} S={S} ts={markScale}/>)}

            {/* load-imbalance flags */}
            {[dispH,dispV].filter(Boolean).flatMap(sc=>(sc.windLoads||[]).filter(w=>w.imbalance).map((w,i)=>{
              const mx=(w.wa.x+w.wb.x)/2, my=(w.wa.y+w.wb.y)/2;
              return <text key={(sc.axis)+i} x={mx+w.nx*4*S} y={my+w.ny*4*S} fill="#B23A2A" fontSize={1.35*S*markScale}
                           fontWeight="700" textAnchor="middle" dominantBaseline="middle">⚠ imbalance</text>;
            }))}

            {/* nodes */}
            {graph.nodes.map(p=>{
              const isSel=p.id===selected;
              return(
                <g key={p.id} style={{cursor:"grab"}} onPointerDown={e=>onNodeLDown(p.id,e)} onContextMenu={e=>openMenu(e,{kind:"node",id:p.id})}>
                  <circle cx={p.x} cy={p.y} r={3.5*S} fill="transparent"/>{/* hit-target kept full size (NOT scaled) so small nodes stay easy to click/grab */}
                  {isSel&&<circle cx={p.x} cy={p.y} r={1.8*S*markScale} fill="rgba(35,87,127,.18)"/>}
                  <circle cx={p.x} cy={p.y} r={(isSel?1.05:0.85)*S*markScale} fill={C_NODE} stroke={C_BG} strokeWidth={0.25*S*markScale}/>{/* rev 32: node dot scales with Markup (base = original pre-rev-31 size) */}
                </g>
              );
            })}

            {/* dimension labels — drawn last so the masked boxes read over any line */}
            {dims&&graph.edges.map(ed=>{
              const a=graph.nodes.find(n=>n.id===ed.a), b=graph.nodes.find(n=>n.id===ed.b);
              if(!a||!b) return null;
              const L=dist(a,b); if(L<4) return null;
              const mx=(a.x+b.x)/2, my=(a.y+b.y)/2, isV=edgeAxis(a,b)==="v";
              const editing=dimEdit&&same(dimEdit.edge,ed);
              return(
                <g key={`d${ed.a}-${ed.b}`} style={{cursor:panMode?"grab":"text"}} onPointerDown={e=>{ if(panMode&&e.button===0){ beginPan(e); return; } e.stopPropagation(); }} onClick={e=>onDimClick(ed,e)}>
                  <Tag x={mx} y={my} text={`${fmtHalf(L)}'`} box={editing?"#9A6B1F":C_DIMBOX} S={S} ts={markScale} rot={isV?-90:0}/>
                </g>
              );
            })}
          </svg>

          {menu&&(
            <div ref={menuRef} className="cmenu" style={{left:menu.x,top:menu.y}}>
              {menu.kind==="canvas"?(
                <>
                  <div className="cmh">Canvas</div>
                  <button className={"cmi"+(drawMode?" act":"")} onClick={()=>{ toggleDrawMode(); closeMenu(); }}>
                    <span className="cmlbl">✏ Draw</span>{drawMode&&<span className="cmck">✓</span>}
                  </button>
                  <button className={"cmi"+(panMode?" act":"")} onClick={()=>{ togglePanMode(); closeMenu(); }}>
                    <span className="cmlbl">✋ Pan</span>{panMode&&<span className="cmck">✓</span>}
                  </button>
                  <button className="cmi cmzoom" onClick={()=>setZoomEnabled(v=>!v)}
                          title={zoomEnabled?"Mouse-wheel zoom is ON — click to turn off":"Mouse-wheel zoom is OFF — click to turn on"}>
                    <span className="cmlbl">🔍 Zoom (wheel)</span>
                    <span className={"cmlight"+(zoomEnabled?" on":"")}/>
                  </button>
                </>
              ):menu.kind==="node"?(
                <>
                  <div className="cmh">Node</div>
                  <button className="cmi" onClick={()=>{
                    const isSel=selRef.current===menu.id;
                    if(isSel) setSelected(null);
                    else { if(selRef.current!==null) connectTo(selRef.current,menu.id); setSelected(menu.id); }
                    closeMenu();
                  }}>{selected===menu.id?"Deselect":"Select"+(selected!==null?" & connect":"")}</button>
                  <button className="cmi del" onClick={()=>{deleteNode(menu.id);closeMenu();}}>Delete node</button>
                </>
              ):(
                <>
                  <div className="cmh">Wall</div>
                  <button className="cmi" onClick={()=>{toggleSupport(menu.edge);closeMenu();}}>
                    {isSup(keyOf(menu.edge)) ? "✓ Takes point load" : "✕ No point load"}
                  </button>
                  {twoStory && (
                    <button className="cmi" onClick={()=>{toggleOneStory(menu.edge);closeMenu();}}>
                      {oneStory.has(keyOf(menu.edge)) ? "↥ Switch to 2-story" : "↧ Switch to 1-story"}
                    </button>
                  )}
                  <button className="cmi" onClick={()=>{ setDlEdit(keyOf(menu.edge)); closeMenu(); }}>⬚ DL Tributary…</button>
                  <button className="cmi" onClick={()=>{splitWall(menu.edge,menu.u);closeMenu();}}>Add node here</button>
                  <button className="cmi del" onClick={()=>{deleteEdge(menu.edge);closeMenu();}}>Delete wall</button>
                </>
              )}
            </div>
          )}

          {dimEdit&&(
            <div ref={dimWrapRef} className="dim-input-wrap" style={{left:dimEdit.px,top:dimEdit.py}}>
              <input className="dim-inp" type="number" min="0.5" step="0.5" value={dimEdit.val} autoFocus
                     onChange={e=>setDimEdit(d=>({...d,val:e.target.value}))}
                     onKeyDown={e=>{ if(e.key==="Enter"){applyWallLength(dimEdit.edge,parseFloat(dimEdit.val),dimEdit.moveEnd);} if(e.key==="Escape"){setDimEdit(null);} }}/>
              <span className="dim-unit">ft</span>
            </div>
          )}
          {/* (rev 71) Tab dynamic-length editor: type the next segment's length; Enter commits it
              exactly along the captured rubber-band heading. Same chrome as the LENGTHEN editor. */}
          {drawLenEdit&&(
            <div className="dim-input-wrap" style={{left:drawLenEdit.px,top:drawLenEdit.py}}>
              <input className="dim-inp" type="number" min="0.5" step="0.5" value={drawLenEdit.val} autoFocus
                     onChange={e=>setDrawLenEdit(d=>({...d,val:e.target.value}))}
                     onKeyDown={e=>{
                       if(e.key==="Enter"){ const v=parseFloat(drawLenEdit.val); if(v>0) commitDrawLength(v); else setDrawLenEdit(null); }
                       else if(e.key==="Escape"){ setDrawLenEdit(null); }
                       else if(e.key==="Tab"){ e.preventDefault(); }   // keep focus in the box
                     }}/>
              <span className="dim-unit">ft</span>
            </div>
          )}
        </div>{/* /stage */}

        </div>{/* /canvascol */}

        {/* side panel */}
        <div className="panel">
          <div className="card">
            <h4>Live Metrics</h4>
            <div className="row"><span>Nodes</span><b>{graph.nodes.length}</b></div>
            <div className="row"><span>Walls</span><b>{graph.edges.length}</b></div>
            <div className="row"><span>Total wall</span><b>{Math.round(totalLen)}<small>ft</small></b></div>
            <div className="row"><span>Enclosed area</span><b>{loop?Math.round(loop.area):"—"}{loop&&<small>ft²</small>}</b></div>
          </div>

          <div className="card">
            <h4>Dead Loads</h4>
            <div className="row">
              <span>Roof DL</span>
              <span style={{display:"flex",alignItems:"center",gap:6}}>
                <input type="number" step={1} min={0} value={g?g.roofDL:0}
                  onChange={(e)=>setGl&&setGl("roofDL",parseFloat(e.target.value)||0)}
                  style={{width:64,padding:"4px 6px",border:"1px solid var(--line)",borderRadius:4,fontSize:13,textAlign:"right",color:"var(--ink)",background:"#FFFFFF"}}/>
                <small style={{color:"var(--muted)"}}>psf</small>
              </span>
            </div>
            <div className="row">
              <span>Floor DL</span>
              <span style={{display:"flex",alignItems:"center",gap:6}}>
                <input type="number" step={1} min={0} value={g?g.floorDL:0}
                  onChange={(e)=>setGl&&setGl("floorDL",parseFloat(e.target.value)||0)}
                  style={{width:64,padding:"4px 6px",border:"1px solid var(--line)",borderRadius:4,fontSize:13,textAlign:"right",color:"var(--ink)",background:"#FFFFFF"}}/>
                <small style={{color:"var(--muted)"}}>psf</small>
              </span>
            </div>
            <div className="row">
              <span>Wall DL</span>
              <span style={{display:"flex",alignItems:"center",gap:6}}>
                <input type="number" step={1} min={0} value={g?g.wallDL:0}
                  onChange={(e)=>setGl&&setGl("wallDL",parseFloat(e.target.value)||0)}
                  style={{width:64,padding:"4px 6px",border:"1px solid var(--line)",borderRadius:4,fontSize:13,textAlign:"right",color:"var(--ink)",background:"#FFFFFF"}}/>
                <small style={{color:"var(--muted)"}}>psf</small>
              </span>
            </div>
            <div className="row" style={{borderTop:"1px solid var(--line)",marginTop:4,paddingTop:6}}>
              <span>Seismic C<sub>s</sub></span>
              <span style={{display:"flex",alignItems:"center",gap:6}}>
                <input type="number" step={0.005} min={0} value={g?(g.Cs ?? 0):0}
                  onChange={(e)=>setGl&&setGl("Cs",parseFloat(e.target.value)||0)}
                  style={{width:64,padding:"4px 6px",border:"1px solid var(--line)",borderRadius:4,fontSize:13,textAlign:"right",color:"var(--ink)",background:"#FFFFFF"}}/>
                <small style={{color:"var(--muted)",width:26}}>coef</small>
              </span>
            </div>
            <p className="hint" style={{marginTop:6,marginBottom:0}}>Roof/Floor/Wall DL feed the seismic weight (this tab) and wall uplift resistance (Design/Calc). C<sub>s</sub> sets the base shear V = C<sub>s</sub>·W.</p>
          </div>

          {!twoStory ? (
            <div className="card">
              <h4>Seismic Weight</h4>
              <div className="row"><span>Roof area</span><b>{loop?Math.round(sw.area).toLocaleString():"—"}{loop&&<small>ft²</small>}</b></div>
              <div className="row"><span>W roof</span><b>{Math.round(sw.Wroof).toLocaleString()}<small>lbs</small></b></div>
              <div className="row"><span>W wall</span><b>{Math.round(sw.Wwall).toLocaleString()}<small>lbs</small></b></div>
              <div className="row" style={{borderTop:"1px solid var(--line)",marginTop:4,paddingTop:6}}>
                <span style={{fontWeight:800}}>W total</span>
                <b style={{color:"var(--accent)"}}>{Math.round(sw.Wtotal).toLocaleString()}<small>lbs</small></b>
              </div>
              <div className="row" style={{marginTop:2}}>
                <span>Base shear V = Cs·W <span style={{color:"var(--muted)"}}>(Cs {Number(g&&g.Cs)||0})</span></span>
                <b style={{color:"var(--hot)"}}>{Math.round((Number(g&&g.Cs)||0)*sw.Wtotal).toLocaleString()}<small>lbs</small></b>
              </div>
              <div className="row" style={{fontSize:11,color:"var(--muted)",marginTop:2}}>
                <span>X-dir face load (⟂ {Math.round(seisExtent.dy)}′)</span><b style={{color:"var(--ink)"}}>{fmt2(wSeisX)}<small>plf</small></b>
              </div>
              <div className="row" style={{fontSize:11,color:"var(--muted)"}}>
                <span>Y-dir face load (⟂ {Math.round(seisExtent.dx)}′)</span><b style={{color:"var(--ink)"}}>{fmt2(wSeisY)}<small>plf</small></b>
              </div>
              <p className="hint" style={{marginTop:6,marginBottom:0}}>Toggle <b>Load case → Seismic</b> (top toolbar) to map these onto the plan boundary as plf line loads + wall reactions.</p>
              {sw.profiles.length>0 && (
                <div style={{marginTop:8}}>
                  <div style={{fontSize:10.5,fontWeight:800,letterSpacing:".04em",textTransform:"uppercase",color:"var(--muted)",marginBottom:4}}>By parapet profile</div>
                  {sw.profiles.map((p,i)=>(
                    <div key={i} className="row" style={{fontSize:11}}>
                      <span style={{color:"var(--muted)"}}>{fmt1(p.par)}′ par · H{fmt1(p.H)}′ · {Math.round(p.len)}′ → Hₜ {fmt1(p.htrib)}′</span>
                      <b>{Math.round(p.w).toLocaleString()}<small>lbs</small></b>
                    </div>
                  ))}
                </div>
              )}
              {!loop && <p className="hint" style={{marginTop:6,marginBottom:0}}>Close the plan boundary to get the roof area.</p>}
            </div>
          ) : (
            <div className="card">
              <h4>Seismic Weight <span style={{fontSize:10,fontWeight:600,color:"var(--muted)"}}>· 2-Story</span></h4>
              {sw2 ? (<>
                {/* per-level effective weights (area DL + tributary wall DL) */}
                <div className="row" style={{fontSize:10.5,fontWeight:800,letterSpacing:".04em",textTransform:"uppercase",color:"var(--muted)",marginBottom:2}}><span>Level</span><span>W · h</span></div>
                <div className="row"><span>Roof (L2) <span style={{color:"var(--muted)"}}>h {fmt1(sw2.hRoof)}′</span></span><b>{Math.round(sw2.Wroof).toLocaleString()}<small>lbs</small></b></div>
                <div className="row" style={{fontSize:11,color:"var(--muted)",marginTop:-2}}>
                  <span>area {Math.round(sw2.WroofArea).toLocaleString()} + wall {Math.round(sw2.WroofWall).toLocaleString()}</span>
                </div>
                <div className="row" style={{marginTop:3}}><span>Floor (L1) <span style={{color:"var(--muted)"}}>h {fmt1(sw2.hFloor)}′</span></span><b>{Math.round(sw2.Wfloor).toLocaleString()}<small>lbs</small></b></div>
                <div className="row" style={{fontSize:11,color:"var(--muted)",marginTop:-2}}>
                  <span>area {Math.round(sw2.WfloorArea).toLocaleString()} + wall {Math.round(sw2.WfloorWall).toLocaleString()}</span>
                </div>
                <div className="row" style={{borderTop:"1px solid var(--line)",marginTop:4,paddingTop:6}}>
                  <span style={{fontWeight:800}}>W total</span>
                  <b style={{color:"var(--accent)"}}>{Math.round(sw2.Wtotal).toLocaleString()}<small>lbs</small></b>
                </div>
                <div className="row" style={{marginTop:2}}>
                  <span>Base shear V = Cs·W <span style={{color:"var(--muted)"}}>(Cs {Cs})</span></span>
                  <b style={{color:"var(--hot)"}}>{Math.round(Cs*sw2.Wtotal).toLocaleString()}<small>lbs</small></b>
                </div>
                {/* Phase 3 — vertical distribution F_x = V·(W·h)/Σ(W·h) */}
                {seis2 && (<>
                  <div className="row" style={{fontSize:10.5,fontWeight:800,letterSpacing:".04em",textTransform:"uppercase",color:"var(--muted)",marginTop:8,marginBottom:2}}><span>Story force F<sub>x</sub></span><span></span></div>
                  <div className="row"><span>F roof (L2)</span><b style={{color:"var(--ink)"}}>{Math.round(seis2.Froof).toLocaleString()}<small>lbs</small></b></div>
                  <div className="row"><span>F floor (L1)</span><b style={{color:"var(--ink)"}}>{Math.round(seis2.Ffloor).toLocaleString()}<small>lbs</small></b></div>
                  {/* Phase 4 — per-level plan plf (face load = F / extent ⟂ the force) */}
                  <div className="row" style={{fontSize:10.5,fontWeight:800,letterSpacing:".04em",textTransform:"uppercase",color:"var(--muted)",marginTop:8,marginBottom:2}}><span>Plan plf · {activeFloor===2?"Roof (L2)":"Floor (L1)"} view</span><span></span></div>
                  <div className="row" style={{fontSize:11,color:"var(--muted)"}}>
                    <span>X-dir face load (⟂ {Math.round(seisViewExtent.dy)}′)</span><b style={{color:"var(--ink)"}}>{fmt2(wSeisX)}<small>plf</small></b>
                  </div>
                  <div className="row" style={{fontSize:11,color:"var(--muted)"}}>
                    <span>Y-dir face load (⟂ {Math.round(seisViewExtent.dx)}′)</span><b style={{color:"var(--ink)"}}>{fmt2(wSeisY)}<small>plf</small></b>
                  </div>
                </>)}
                <p className="hint" style={{marginTop:6,marginBottom:0}}>The <b>Plan plf</b> follows the <b>floor selector</b> (below the canvas) — Level 2 shows the roof diaphragm, Level 1 the floor diaphragm. Toggle <b>Load case → Seismic</b> to map them onto the plan boundary as plf loads + wall reactions.</p>
                {!loop && <p className="hint" style={{marginTop:6,marginBottom:0}}>Close the plan boundary to get the diaphragm areas.</p>}
              </>) : (
                <p className="hint" style={{marginTop:0,marginBottom:0}}>Draw a closed plan to compute the per-diaphragm seismic weight.</p>
              )}
            </div>
          )}

          {(secH||secV)&&(
            <div className="card">
              <h4>Wind Line Loads</h4>
              {[["h","E–W",secH],["v","N–S",secV]].map(([o,lbl,sc])=> sc&&sc.windLoads.length?(
                <div key={o} style={{marginBottom:8}}>
                  <div className="row">
                    <span>{lbl} wind</span>
                    <b style={{color:"#9A6B1F"}}>{fmt2(sc.baseShear||0)}<small>k base shear</small></b>
                  </div>
                  <div className="row" style={{fontSize:11,color:"#6B7684"}}>
                    <span>{sc.windLoads.length} windward wall{sc.windLoads.length===1?"":"s"} · tap a load to edit</span>
                  </div>
                  {sc.imbalance && (
                    <div style={{fontSize:11,color:"#B23A2A",fontWeight:600,padding:"2px 0"}}>⚠ Load imbalance — no point-load walls</div>
                  )}
                  <div className="brow" style={{marginTop:4}}>
                    <button className="btn" onClick={()=>{ if(sc.windLoads[0]) setActiveWall({axis:o,key:sc.windLoads[0].key}); }}>Edit</button>
                    <button className="btn pink" onClick={()=>{ setSections(s=>({...s,[o]:null})); setActiveWall(a=>a&&a.axis===o?null:a); }}>Remove</button>
                  </div>
                </div>
              ):null)}
              {onDesignShearWalls && (secH&&secH.reactions.length || secV&&secV.reactions.length) ? (
                <button className="btn"
                  title={designStaleHint ? "Plan changed since you last sent it — click to update the Design tab" : undefined}
                  style={{width:"100%",marginTop:6,fontWeight:700,
                          ...(designStaleHint ? {background:STALE_BTN.background,borderColor:STALE_BTN.borderColor,color:STALE_BTN.color}
                                              : {background:"#23577F",borderColor:"#23577F",color:"#FFFFFF"})}}
                  onClick={runDesignHandoff}>
                  {designStaleHint && WARN}Design shear walls →
                </button>
              ):null}
            </div>
          )}

          <div className="card">
            <h4>Presets</h4>
            <div className="brow">{Object.keys(PRESETS).map(k=>(<button key={k} className="btn" onClick={()=>loadPreset(k)}>{k}</button>))}</div>
            <div className="brow" style={{marginTop:6}}>
              <button className="btn" onClick={undo}>Undo</button>
            </div>
          </div>

          <div className="card">
            <p className="hint">
              <b>✏ Draw walls</b>: click to chain straight walls; click an existing node to connect/close; right-click ends the chain, then right-click again opens the Canvas menu; Esc exits.<br/>
              <b>Left-drag</b> nodes/walls to move.<br/>
              <b>Drag across empty space</b> in a direction to set the wind — it loads every windward wall in that direction.<br/>
              <b>Right-click</b> a node (select/connect/delete) or wall (add node/delete); <b>right-click empty space</b> for the Canvas menu — Draw, Pan (left-drag hand tool), and a Zoom toggle (green light = wheel-zoom on).<br/>
              <b>Click a dimension</b> to edit length.<br/>
              <b>Navigate</b>: scroll the mouse wheel to zoom toward the cursor (toggle in the Canvas menu), middle-drag <i>or</i> the Pan tool to pan, <b>⊡ Fit</b> to frame the whole plan.
            </p>
          </div>
        </div>
      </div>

      {/* ── STATUS BAR — coordinates, mode, toggles, plan stats ── */}
      <div className="statusbar">
        <span className="stcoord">{cursorFt ? `X ${cursorFt.x.toFixed(1)}′  Y ${cursorFt.y.toFixed(1)}′` : "X —  Y —"}</span>
        <span className={"stmode"+(drawMode?" draw":panMode?" pan":"")}>{drawMode ? (drawAnchor!==null?"DRAW · chaining":"DRAW") : panMode ? "PAN" : "SELECT"}</span>
        <span className={"stflag"+(snapOn?" on":"")} onClick={()=>setSnapOn(v=>!v)}>SNAP</span>
        <span className={"stflag"+(ortho?" on":"")} onClick={()=>setOrtho(v=>!v)}>ORTHO</span>
        <span className="stright">
          {graph.edges.length} walls · {Math.round(totalLen)}′
          {secH&&secH.windLoads.length?` · E–W ${fmt2(secH.baseShear||0)}k`:""}
          {secV&&secV.windLoads.length?` · N–S ${fmt2(secV.baseShear||0)}k`:""}
        </span>
      </div>

      {activeWall&&activeSection&&(
        <WindWindow key={activeWall.key+"|"+(activeLeeKey||"")} section={activeSection}
                    setVals={setVals} onReverse={reverseWind}
                    onClose={()=>setActiveWall(null)} onRemove={removeSection}
                    twoStory={twoStory} oneStory={isOneStory(activeWall.key)}/>
      )}

      {dlEdit&&(
        <DLTributaryWindow key={dlEdit+"|"+activeFloor+"|"+(isOneStory(dlEdit)?"1s":"2s")} wprops={propsFor(dlEdit)}
                    twoStory={twoStory} activeFloor={activeFloor} oneStory={isOneStory(dlEdit)}
                    onSet={(patch)=>setVals(dlEdit, patch)} onClose={()=>setDlEdit(null)}/>
      )}

      {globalInputs&&(
        <GlobalInputsWindow key={twoStory?"gi2":"gi1"} seed={globalInputs} twoStory={twoStory}
                    hasOneStory={oneStory.size>0}
                    onApply={applyGlobalInputs} onClose={()=>setGlobalInputs(null)}/>
      )}
    </div>
  );
}

/* ════════════════════════════════════════════════════════════════════════
   PLYWOOD SHEAR WALL MODULE (merged from shear-wall-calculator)
   Engine is a verbatim port of "Plywood Shear Wall - Wood Studs.xlsx" — as of
   the rev-33 split it lives in ./calcCore.js (calcSegment, generateDesign,
   baseDesignSeg, schedFor, HD_TABLE, NAIL_EDGE, CODES, isNum, xMax, numOr0,
   imported at the top of this file). The engine is byte-identical to before.
   Calculation Sheet tab: unchanged logic, restyled to the sketcher theme.
   Design tab: rebuilt around the sketcher plan — per-line optimization,
   drag-in-plan shear walls, right-click overrides (holdown/nailing/post).
   ════════════════════════════════════════════════════════════════════════ */

// ---------- Formatting + dark theme (sketcher palette first) ----------
const fmt = (v, d = 0) => {
  if (v === "neglect") return "neglect";
  if (!isNum(v)) return typeof v === "string" ? v : "—";
  return v.toLocaleString("en-US", { minimumFractionDigits: d, maximumFractionDigits: d });
};
const SW = {  // light drafting palette — matches the Calculation Sheet (LT) scheme
  page:"#EFEDE6", sheet:"#FFFFFF", panel:"#FFFFFF", ink:"#1C2733", faint:"#586470",
  rule:"#D8D4C8", accent:"#23577F", accentSoft:"#E8EFF4",
  red:"#B23A2A", redSoft:"#F8E9E5", green:"#2E6B4F", greenSoft:"#E7F1EB",
  amber:"#8A5E16", amberSoft:"#F7EEDC", wall:"#1C2733", input:"#FDFDFB",
};
const MONO = "'IBM Plex Mono', ui-monospace, 'SF Mono', Menlo, Consolas, monospace";

function Chip({ v, d = 0, suffix = "" }) {
  let bg = "transparent", color = SW.ink, text = fmt(v, d);
  if (v === "FAILED!!!" || v === "NG!" || v === "NG!!") { bg = SW.redSoft; color = SW.red; }
  else if (v === "neglect") { bg = SW.amberSoft; color = SW.amber; }
  else if (v === "None" || v === "—" || v === "Simpson" || v === "Threaded") { color = SW.faint; }
  else if (v === "OK") { bg = SW.greenSoft; color = SW.green; }
  return (
    <span style={{ background:bg, color, fontFamily:MONO, fontSize:12, padding:bg==="transparent"?0:"1px 6px", borderRadius:3, whiteSpace:"nowrap", fontWeight:bg!=="transparent"?600:400 }}>
      {text}{suffix && isNum(v) ? suffix : ""}
    </span>
  );
}
function Row({ label, unit, cells, render }) {
  return (
    <tr style={{ borderBottom: `1px solid ${SW.rule}` }}>
      <td style={{ padding:"5px 10px", fontSize:12, color:SW.ink, whiteSpace:"nowrap" }}>
        {label} {unit && <span style={{ color:SW.faint, fontSize:11 }}>({unit})</span>}
      </td>
      {cells.map((r, i) => (
        <td key={i} style={{ padding:"5px 8px", textAlign:"right" }}>
          {r.active ? render(r, i) : <span style={{ color:SW.rule }}>·</span>}
        </td>
      ))}
    </tr>
  );
}
function SectionTitle({ children, right }) {
  return (
    <div style={{ display:"flex", alignItems:"center", gap:10, margin:"26px 0 8px" }}>
      <span style={{ width:6, height:6, background:SW.accent, display:"inline-block", flex:"none" }} aria-hidden="true"/>
      <div style={{ fontSize:11, fontWeight:700, letterSpacing:"0.14em", textTransform:"uppercase", color:SW.accent }}>{children}</div>
      <div style={{ flex:1, height:1, background:SW.rule }} />
      {right}
    </div>
  );
}
function NumInput({ value, onChange, step = 1, width = 64, style }) {
  return (
    <input type="number" step={step} value={value}
      onChange={(e) => onChange(parseFloat(e.target.value) || 0)}
      style={{ width, padding:"3px 6px", border:`1px solid ${SW.rule}`, borderRadius:4, fontFamily:MONO, fontSize:12,
               textAlign:"right", color:SW.accent, fontWeight:600, background:SW.input, outline:"none", ...style }} />
  );
}
// Grouped constraint card — visual twin of the calc sheet's "Design loads" cards (LtCollapse flex cards)
function ConGroup({ title, children }) {
  return (
    <div style={{ flex:"1 1 200px", border:`1px solid ${SW.rule}`, borderRadius:6, padding:"6px 10px 8px", background:SW.panel }}>
      <div style={{ fontSize:10, fontWeight:700, letterSpacing:"0.08em", textTransform:"uppercase", marginBottom:4, color:SW.ink }}>{title}</div>
      <div style={{ display:"flex", flexWrap:"wrap", gap:"6px 12px", alignItems:"flex-end" }}>{children}</div>
    </div>
  );
}
function SwField({ label, children }) {
  return (
    <label style={{ display:"flex", flexDirection:"column", gap:3 }}>
      <span style={{ fontSize:10, letterSpacing:"0.1em", textTransform:"uppercase", color:SW.faint }}>{label}</span>
      {children}
    </label>
  );
}
const selStyle = { padding:"3px 4px", border:`1px solid ${SW.rule}`, borderRadius:4, fontSize:11, fontFamily:MONO,
                   color:SW.accent, fontWeight:600, background:SW.input, outline:"none" };
// Pinned-constraints panel: every control shares one height + font so the rows line up (rev 8)
const CON_H = 24;
const conNum = { height:CON_H, boxSizing:"border-box" };
const conSel = { ...selStyle, fontSize:12, padding:"2px 4px", height:CON_H, boxSizing:"border-box", minWidth:56, maxWidth:158 };

// ── Pinned-panel field system (rev 11) ──────────────────────────────────────
// Inline label-left / control-right rows inside a CSS grid. One line per field
// (half the height of stacked label-on-top), controls share a column edge so
// everything aligns, and a fixed unit gutter keeps numbers and units tidy.
const PIN_H = 22;
const pinCard = { border:`1px solid ${SW.rule}`, borderRadius:6, padding:"5px 9px 6px", background:SW.panel, minWidth:0 };
const pinTitle = { fontSize:10.5, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom:4, color:SW.ink };
const pinNumS = { width:46, height:PIN_H, boxSizing:"border-box", padding:"0 5px", border:`1px solid ${SW.rule}`, borderRadius:4,
                  fontFamily:MONO, fontSize:11, textAlign:"right", color:SW.accent, fontWeight:600, background:SW.input, outline:"none" };
const pinSelS = { height:PIN_H, boxSizing:"border-box", padding:"0 2px", border:`1px solid ${SW.rule}`, borderRadius:4,
                  fontFamily:MONO, fontSize:11, color:SW.accent, fontWeight:600, background:SW.input, outline:"none", minWidth:46 };
function PinCard({ title, cols = 2, grow, children }) {
  return (
    <div style={pinCard}>
      <div style={pinTitle}>{title}</div>
      <div style={{ display:"grid", gridTemplateColumns:`repeat(${cols}, minmax(0,1fr))`, columnGap:12, rowGap:5 }}>{children}</div>
    </div>
  );
}
// label truncates with ellipsis (full text in title) so no label can ever break the row; unit sits in a fixed right gutter.
function PinRow({ label, unit = "", full, grow, children }) {
  return (
    <label title={label} style={{ display:"flex", alignItems:"center", gap:6, minWidth:0, gridColumn: full ? "1 / -1" : "auto" }}>
      <span style={{ flex: grow ? "0 0 auto" : "1 1 auto", minWidth:0, fontSize:8.5, letterSpacing:"0.02em",
                     textTransform:"uppercase", color:SW.faint, whiteSpace:"nowrap", overflow:"hidden", textOverflow:"ellipsis" }}>{label}</span>
      <span style={{ flex: grow ? "1 1 auto" : "none", display:"flex", alignItems:"center", gap:3, minWidth:0 }}>
        {children}
        <span style={{ width:13, flex:"none", fontSize:8.5, color:SW.faint, textAlign:"left" }}>{unit}</span>
      </span>
    </label>
  );
}
const swBtn = (primary) => ({
  padding:"8px 16px", fontSize:12, fontWeight:700, letterSpacing:"0.06em",
  border:`1.5px solid ${primary ? SW.accent : SW.rule}`, background: primary ? SW.accent : SW.panel,
  color: primary ? "#FFFFFF" : SW.ink, cursor:"pointer", borderRadius:4,
});

/* ── STALE-PUSH INDICATOR (rev 130) ──────────────────────────────────────────
   A "push data" button (Plan→Design ⚡, Design→Calc →) goes red when the upstream
   inputs have changed since the LAST time you pushed, so re-pushing would change
   the downstream tab. (rev 153) Recolored RED → AMBER so "needs re-run" no longer
   collides with the engineering-FAIL red used by capacity chips/hatching — red now
   means failure ONLY; amber means "stale, click to refresh". Pale-amber wash + amber
   border keep the amber text (AA 5.0 on the wash) legible over any base fill. Applied
   inline so it overrides whatever base style/class the button already carries. */
const STALE_BTN = { color:"#8A5E16", background:"#FBF0D8", border:"1.5px solid #C08A2A", borderColor:"#C08A2A", fontWeight:700 };

// Signature of exactly what `applyToCalc` would push to the Calculation Sheet for a
// given design line: the segment lengths, the line's force/height/tributary, the
// per-segment selected schedule types, and the constraint fields the sheet seeds
// from. Two calls are equal iff re-sending would produce the same sheet — so an edit
// that wouldn't change the push (or an edit-then-revert) leaves the signature alone.
// (g is App-level shared state, read live by the calc sheet, so it is NOT part of the
//  push and is intentionally excluded — except via selType, which the sheet snapshots.)
function calcPushSig(line, segs, res, dC){
  return JSON.stringify({
    f: Math.round((line && line.forceLbs) || 0),
    h: line ? line.heightFt : null,
    rt: (line && line.roofTrib != null)  ? line.roofTrib  : (dC ? dC.roofTrib  : null),
    ft: (line && line.floorTrib != null) ? line.floorTrib : (dC ? dC.floorTrib : null),
    segs: (segs || []).map(s => s.length),
    types: (res || []).map(r => (r && isNum(r.selType)) ? Math.min(r.selType, 6) : 1),
    d: dC ? [dC.hdDist, dC.thickness, dC.anchor, dC.ftgWidth, dC.ftgThick] : [],
  });
}

// rev 130b — the caution sign prefixed to a stale button's label. U+FE0E (text-presentation
// selector) forces a MONOCHROME triangle that inherits the button's text color — now the rev-153
// AMBER stale color (rather than the yellow emoji), so it reads as part of the "stale" styling. It sits INLINE to the left of the
// label with a trailing space, so it never overlaps or obstructs the text (swap to "⚠️ " for the
// classic yellow emoji if preferred).
const WARN = "\u26A0\uFE0E ";

// Signature of the inputs the Design-tab "⚡ Optimize design" optimizer (optimizeAll) consumes, so the
// button can go red when re-optimizing would produce a different design. Covers every line's
// force/height/length/tributary across BOTH floors + the framing/code (g) + the design constraints (d).
// g.wWind is EXCLUDED — optimizeAll overrides it per-line with the line's own force (so a calc-sheet
// push that sets g.wWind must NOT mark Optimize stale); g.line is a cosmetic label, also excluded.
function optimizeSig(linesByFloor, lines, twoStory, g, d){
  const f1 = (linesByFloor && linesByFloor[1]) || (twoStory ? [] : (lines || [])) || [];
  const f2 = (twoStory && linesByFloor && linesByFloor[2]) || [];
  const key = (l) => [l.id, Math.round(l.forceLbs || 0), Math.round(l.forceLbsSeismic || 0), l.heightFt, l.lengthFt, l.roofTrib, l.floorTrib];
  const gKey = { ...(g || {}) }; delete gKey.wWind; delete gKey.line;
  return JSON.stringify({ f1: f1.map(key), f2: f2.map(key), g: gKey, d: d || {} });
}

/* ────────────────────────────────────────────────────────────────────────
   LIGHT THEME — Calculation Sheet only. 1:1 port of the standalone
   shear-wall-calculator app (paper page, white sheet, compliance banner,
   D/C utilization bars, collapsible sections, sticky row labels, column
   highlight, formula tooltips, print). Namespaced Lt- / LT- so the dark
   Design tab components above are untouched.
   ──────────────────────────────────────────────────────────────────────── */
// Utilization (UI layer) — derives D/C ratios + pass verdict from an engine
// result WITHOUT touching calcSegment (engine stays verbatim per handoff §2).
function withUtil(r, seg, grade) {
  if (!r || !r.active) return r;
  const selT = schedFor(grade)[Math.max(0, Math.min(5, (seg.selType || 1) - 1))];
  const utilW = r.vW / selT.wind;
  const utilS = r.vS / (r.factor * selT.seismic);
  const { Pa224, Pa44, Pa226, Pa46, Pa66, Pa68 } = r.Pa;
  const postCap =
    r.post === "(2) 2x4" ? Pa224 : r.post === "4x4" ? Pa44 : r.post === "(2) 2x6" ? Pa226
    : r.post === "4x6" ? Pa46 : r.post === "6x6" ? Pa66 : r.post === "6x8" ? Pa68
    : seg.thickness <= 4 ? (Pa46 * 3.5) / 5.5 : Pa68; // NG! → largest available
  const utilPost = r.maxComp / postCap;
  const hdEntry = HD_TABLE.find((x) => r.hd.includes(x.name));
  const utilHD = r.maxUplift === 0 ? 0 : hdEntry ? r.maxUplift / hdEntry.cap : r.maxUplift / HD_TABLE[5].cap;
  const pass = r.status === "OK" && !r.aspectNG && r.post !== "NG!" && r.hd !== "NG!" && r.anchorSel !== "NG!!";
  return { ...r, utilW, utilS, utilPost, utilHD, pass };
}

const LT = {
  paper: "#EFEDE6", sheet: "#FFFFFF", ink: "#1C2733", faint: "#586470",
  rule: "#D8D4C8", blue: "#23577F", blueSoft: "#E8EFF4",
  red: "#B23A2A", redSoft: "#F8E9E5", green: "#2E6B4F", greenSoft: "#E7F1EB",
  amber: "#8A5E16", amberSoft: "#F7EEDC", zebra: "#FAF9F5", hover: "#F1F4F6",
};

const LT_CSS = `
  .sw-table { border-collapse: collapse; width: 100%; min-width: 760px; }
  .sw-table td, .sw-table th { background: ${LT.sheet}; }
  .sw-table td:first-child, .sw-table th:first-child {
    position: sticky; left: 0; z-index: 2;
    box-shadow: 2px 0 0 ${LT.rule};
  }
  .sw-table thead th { background: #F7F6F1; border-bottom: 1.5px solid ${LT.ink}; }
  .sw-table td { transition: background .12s ease; }
  .sw-table tbody tr:nth-child(even) td { background: ${LT.zebra}; }
  .sw-table tbody tr:hover td { background: ${LT.hover}; }
  .sw-table td.sw-hl, .sw-table th.sw-hl { background: ${LT.blueSoft} !important; }
  .sw-scroll { overflow-x: auto; border: 1px solid ${LT.rule}; }
  button:focus-visible, input:focus-visible, select:focus-visible, svg:focus-visible, [tabindex]:focus-visible {
    outline: 2px solid ${LT.blue}; outline-offset: 1px;
  }
  @media (prefers-reduced-motion: no-preference) {
    .sw-collapse-body { animation: swFade 0.15s ease-out; }
    @keyframes swFade { from { opacity: 0.4; } to { opacity: 1; } }
  }
  /* rev 132 — Calculation Sheet sub-tab bar (Chrome-style) */
  .calctab { transition: background .12s, color .12s; }
  .calctab:not(.is-active):hover { background: #F1F4F6; color: #1C2733; }
  .calctab-x { opacity: 0; transition: opacity .12s, background .12s; }
  .calctab:hover .calctab-x, .calctab.is-active .calctab-x { opacity: .6; }
  .calctab-x:hover { opacity: 1 !important; background: #E2E6E9; color: #1C2733; }
  .calc-add { transition: background .12s; }
  .calc-add:hover { background: #EDF1F4; }
  @media print {
    .no-print { display: none !important; }
    .sw-scroll { overflow: visible; border: none; }
    body { background: #FFF !important; }
  }
`;

function LtChip({ v, d = 0 }) {
  let bg = "transparent", color = LT.ink, text = fmt(v, d);
  if (v === "FAILED!!!" || v === "NG!" || v === "NG!!") { bg = LT.redSoft; color = LT.red; }
  else if (v === "neglect") { bg = LT.amberSoft; color = LT.amber; }
  else if (v === "None" || v === "—" || v === "Simpson" || v === "Threaded") { color = LT.faint; }
  else if (v === "OK") { bg = LT.greenSoft; color = LT.green; }
  return (
    <span style={{ background: bg, color, fontFamily: MONO, fontSize: 12, padding: bg === "transparent" ? 0 : "1px 6px", borderRadius: 3, whiteSpace: "nowrap", fontWeight: bg !== "transparent" ? 600 : 400 }}>
      {text}
    </span>
  );
}

function LtUtilBar({ ratio }) {
  if (!isNum(ratio)) return <LtChip v="—" />;
  const over = ratio > 1;
  const pct = Math.min(ratio, 1.25) / 1.25 * 100;
  const color = over ? LT.red : ratio > 0.85 ? LT.amber : LT.green;
  const fillBg = over
    ? "repeating-linear-gradient(135deg, #B23A2A 0 6px, #C5503F 6px 12px)"   // hatched when exceeding capacity
    : `linear-gradient(180deg, ${color} 0%, ${color} 60%, rgba(0,0,0,0.08) 100%)`;
  return (
    <span style={{ display: "inline-flex", alignItems: "center", gap: 7 }}>
      <span style={{ position: "relative", width: 72, height: 9, background: "#E7E4DA", borderRadius: 99,
                     overflow: "hidden", flex: "none", boxShadow: "inset 0 1px 1.5px rgba(28,39,51,0.12)" }}>
        <span style={{ position: "absolute", left: 0, top: 0, bottom: 0, width: `${pct}%`, background: fillBg,
                       borderRadius: 99, transition: "width .3s cubic-bezier(.22,.61,.36,1)" }} />
        <span style={{ position: "absolute", left: `${100 / 1.25}%`, top: -1, bottom: -1, width: 2,
                       background: LT.ink, opacity: 0.42, transform: "translateX(-1px)" }} title="100% capacity" />
      </span>
      <span style={{ fontFamily: MONO, fontSize: 11, color, fontWeight: 700, minWidth: 38, textAlign: "right",
                     fontVariantNumeric: "tabular-nums" }}>{over ? "▲" : ""}{(ratio * 100).toFixed(0)}%</span>
    </span>
  );
}

const HL = React.createContext({ sel: null, setSel: () => {} });

function LtRow({ label, unit, tip, cells, render }) {
  const { sel } = React.useContext(HL);
  return (
    <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
      <td title={tip} style={{ padding: "5px 10px", fontSize: 12, color: LT.ink, whiteSpace: "nowrap", cursor: tip ? "help" : "default" }}>
        {label} {unit && <span style={{ color: LT.faint, fontSize: 11 }}>({unit})</span>}
      </td>
      {cells.map((r, i) => (
        <td key={i} className={sel === i ? "sw-hl" : ""} style={{ padding: "5px 8px", textAlign: "right" }}>
          {r.active ? render(r, i) : <span style={{ color: LT.rule }}>·</span>}
        </td>
      ))}
    </tr>
  );
}

// (rev 132) `marks` (when present) maps a segment index → the SAME wall mark the Design tab shows
// (e.g. "A","B"), so a wall pushed from Design reads identically here ("SW-A", not "SW-1"). A manual
// sub-tab has no Design line → marks is null → falls back to the 1-based numbering, unchanged.
const swMark = (marks, i) => "SW-" + ((marks && marks[i] != null && marks[i] !== "") ? marks[i] : i + 1);
function LtSegHeader({ segments, marks }) {
  const { sel, setSel } = React.useContext(HL);
  return (
    <thead>
      <tr style={{ borderBottom: `1.5px solid ${LT.ink}` }}>
        <th style={{ textAlign: "left", padding: "4px 10px", fontSize: 11 }}></th>
        {segments.map((s, i) => (
          <th
            key={i} className={sel === i ? "sw-hl" : ""}
            onClick={() => setSel(sel === i ? null : i)}
            style={{ padding: "4px 8px", fontSize: 11, fontFamily: MONO, cursor: "pointer", color: (s.length ?? s) > 0 ? LT.blue : LT.faint }}
            title="Click to highlight this wall in all tables"
          >
            {swMark(marks, i)}
          </th>
        ))}
      </tr>
    </thead>
  );
}

function LtCollapse({ title, badge, right, defaultOpen = true, children }) {
  const [open, setOpen] = useState(defaultOpen);
  return (
    <div>
      <div style={{ display: "flex", alignItems: "center", gap: 10, margin: "22px 0 8px" }}>
        <button
          onClick={() => setOpen(!open)}
          style={{ display: "flex", alignItems: "center", gap: 8, background: "none", border: "none", padding: 0, cursor: "pointer" }}
        >
          <span style={{ fontSize: 10, color: LT.blue, transform: open ? "rotate(90deg)" : "none", transition: "transform 0.12s", display: "inline-block" }}>▶</span>
          <span style={{ fontSize: 11, fontWeight: 700, letterSpacing: "0.14em", textTransform: "uppercase", color: LT.blue }}>{title}</span>
          {badge}
        </button>
        <div style={{ flex: 1, height: 1, background: LT.rule }} />
        {right}
      </div>
      {open && <div className="sw-collapse-body">{children}</div>}
    </div>
  );
}

function LtNumInput({ value, onChange, step = 1, width = 64 }) {
  return (
    <input
      type="number" step={step} value={value}
      onChange={(e) => onChange(parseFloat(e.target.value) || 0)}
      style={{ width, padding: "3px 6px", border: `1px solid ${LT.rule}`, borderRadius: 4, fontFamily: MONO, fontSize: 12, textAlign: "right", color: LT.blue, fontWeight: 600, background: "#FDFDFB", outline: "none" }}
    />
  );
}

const ltSel = { padding: "3px 4px", border: `1px solid ${LT.rule}`, borderRadius: 4, fontSize: 11, fontFamily: MONO, color: LT.blue, fontWeight: 600, background: "#FDFDFB", outline: "none" };

function LtComplianceBanner({ segments, results, marks }) {
  const { sel, setSel } = React.useContext(HL);
  const act = results.map((r, i) => ({ r, i })).filter((x) => x.r.active);
  if (!act.length) return null;
  const fails = act.filter((x) => !x.r.pass);
  const allOK = fails.length === 0;
  return (
    <div style={{ display: "flex", flexWrap: "wrap", alignItems: "center", gap: 10, marginTop: 14, padding: "10px 14px", border: `1.5px solid ${allOK ? LT.green : LT.red}`, background: allOK ? LT.greenSoft : LT.redSoft }}>
      <span style={{ fontFamily: MONO, fontSize: 13, fontWeight: 800, color: allOK ? LT.green : LT.red }}>
        {allOK ? "✓ ALL WALLS PASS" : `✕ ${fails.length} OF ${act.length} WALL${act.length > 1 ? "S" : ""} FAILING`}
      </span>
      <span style={{ flex: 1 }} />
      {act.map(({ r, i }) => (
        <button
          key={i} onClick={() => setSel(sel === i ? null : i)}
          title={r.pass ? "Passing — click to highlight" : `Failing: ${[r.aspectNG && "aspect", r.status !== "OK" && "shear/type", r.post === "NG!" && "post", r.hd === "NG!" && "holdown"].filter(Boolean).join(", ")} — click to highlight`}
          style={{
            fontFamily: MONO, fontSize: 11, fontWeight: 700, padding: "3px 9px", cursor: "pointer", borderRadius: 3,
            border: `1.5px solid ${r.pass ? LT.green : LT.red}`,
            background: sel === i ? (r.pass ? LT.green : LT.red) : "#FFF",
            color: sel === i ? "#FFF" : r.pass ? LT.green : LT.red,
          }}
        >
          {swMark(marks, i)} {r.pass ? "✓" : "✕"}
        </button>
      ))}
    </div>
  );
}

function LtElevation({ segments, results, marks }) {
  const { sel, setSel } = React.useContext(HL);
  const active = segments.map((s, i) => ({ ...s, r: results[i], i })).filter((s) => s.length > 0);
  if (!active.length) return null;
  const totalL = active.reduce((a, s) => a + s.length, 0);
  const maxH = Math.max(...active.map((s) => s.height));
  const W = 700, H = 130, gap = 8;
  const scaleX = (W - gap * (active.length - 1)) / totalL;
  const scaleY = 100 / maxH;
  let x = 0;
  return (
    <svg viewBox={`0 0 ${W} ${H}`} style={{ width: "100%", maxWidth: 760, display: "block" }}>
      <line x1="0" y1={H - 18} x2={W} y2={H - 18} stroke={LT.ink} strokeWidth="2" />
      {active.map((s) => {
        const w = s.length * scaleX, h = s.height * scaleY;
        const failed = !s.r.pass;
        const isSel = sel === s.i;
        const el = (
          <g key={s.i} transform={`translate(${x},0)`} style={{ cursor: "pointer" }} onClick={() => setSel(isSel ? null : s.i)}>
            <rect x="0" y={H - 18 - h} width={w} height={h} fill={failed ? LT.redSoft : LT.blueSoft} stroke={failed ? LT.red : LT.blue} strokeWidth={isSel ? 3 : 1.5} />
            <line x1="0" y1={H - 18 - h} x2={w} y2={H - 18} stroke={failed ? LT.red : LT.blue} strokeWidth="0.75" opacity="0.5" />
            <line x1={w} y1={H - 18 - h} x2="0" y2={H - 18} stroke={failed ? LT.red : LT.blue} strokeWidth="0.75" opacity="0.5" />
            <text x={w / 2} y={H - 18 - h / 2 - 4} textAnchor="middle" fontSize="11" fontWeight="700" fill={failed ? LT.red : LT.blue} fontFamily={MONO}>{swMark(marks, s.i)}</text>
            <text x={w / 2} y={H - 18 - h / 2 + 9} textAnchor="middle" fontSize="9" fill={LT.faint} fontFamily={MONO}>{s.length}′ × {s.height}′</text>
            <text x={w / 2} y={H - 5} textAnchor="middle" fontSize="9" fill={LT.faint} fontFamily={MONO}>{failed ? "✕" : "✓"} type {s.selType}</text>
          </g>
        );
        x += w + gap;
        return el;
      })}
    </svg>
  );
}

// ---------- Wall elevation diagram (calc tab) — unchanged logic ----------
function Elevation({ segments, results }) {
  const active = segments.map((s, i) => ({ ...s, r: results[i], i })).filter((s) => s.length > 0);
  if (!active.length) return null;
  const totalL = active.reduce((a, s) => a + s.length, 0);
  const maxH = Math.max(...active.map((s) => s.height));
  const W = 700, H = 130, gap = 8;
  const scaleX = (W - gap * (active.length - 1)) / totalL;
  const scaleY = 100 / maxH;
  let x = 0;
  return (
    <svg viewBox={`0 0 ${W} ${H}`} style={{ width:"100%", maxWidth:760, display:"block" }}>
      <line x1="0" y1={H-18} x2={W} y2={H-18} stroke={SW.faint} strokeWidth="2" />
      {active.map((s) => {
        const w = s.length * scaleX, h = s.height * scaleY;
        const failed = s.r.status === "FAILED!!!" || s.r.aspectNG;
        const stroke = failed ? SW.red : SW.accent;
        const el = (
          <g key={s.i} transform={`translate(${x},0)`}>
            <rect x="0" y={H-18-h} width={w} height={h} fill={failed ? SW.redSoft : SW.accentSoft} stroke={stroke} strokeWidth="1.5" />
            <line x1="0" y1={H-18-h} x2={w} y2={H-18} stroke={stroke} strokeWidth="0.75" opacity="0.5" />
            <line x1={w} y1={H-18-h} x2="0" y2={H-18} stroke={stroke} strokeWidth="0.75" opacity="0.5" />
            <text x={w/2} y={H-18-h/2-4} textAnchor="middle" fontSize="11" fontWeight="700" fill={stroke} fontFamily={MONO}>SW-{s.i+1}</text>
            <text x={w/2} y={H-18-h/2+9} textAnchor="middle" fontSize="9" fill={SW.faint} fontFamily={MONO}>{s.length}′ × {s.height}′</text>
            <text x={w/2} y={H-5} textAnchor="middle" fontSize="9" fill={SW.faint} fontFamily={MONO}>{failed ? "✕" : "✓"} type {s.selType}</text>
          </g>
        );
        x += w + gap;
        return el;
      })}
    </svg>
  );
}

// ---------- CALCULATION SHEET TAB — logic & structure unchanged; dark restyle ----------
function CalcSheet({ g, setGl, segments, setSegments, results, totalL, marks }) {
  const setSeg = (i, key, val) =>
    setSegments((prev) => prev.map((s, j) => (j === i ? { ...s, [key]: val } : s)));
  const E_seis = 0.7 * g.vSeismic;  // rev 61: mirrors calcCore — vSeismic is the post-R reduced base shear; /R dropped
  const F_wind = g.code >= 3 ? 0.6 * g.wWind : g.wWind;

  const failBadge = (cond) =>
    cond ? <span style={{ fontFamily: MONO, fontSize: 10, fontWeight: 700, color: LT.red, background: LT.redSoft, padding: "1px 6px", borderRadius: 3 }}>✕</span> : null;
  const anyFail = {
    shear: results.some((r) => r.active && (r.status === "FAILED!!!" || r.aspectNG)),
    post: results.some((r) => r.active && r.post === "NG!"),
    hd: results.some((r) => r.active && (r.hd === "NG!" || r.anchorSel === "NG!!")),
  };

  return (
    <div>
      <LtComplianceBanner segments={segments} results={results} marks={marks} />

      <LtCollapse title="Design loads">
        <div style={{ display: "flex", flexWrap: "wrap", gap: 16 }}>
          <div style={{ flex: "1 1 260px", border: `1px solid ${LT.rule}`, padding: "10px 14px" }}>
            <div style={{ fontSize: 11, fontWeight: 700, marginBottom: 8 }}>Seismic</div>
            <table style={{ fontSize: 12, width: "100%" }}><tbody>
              <tr><td>V<sub>SEISMIC</sub> (lbs)</td><td style={{ textAlign: "right" }}><LtNumInput value={g.vSeismic} onChange={(v) => setGl("vSeismic", v)} /></td></tr>
              <tr><td>S<sub>DS</sub></td><td style={{ textAlign: "right" }}><LtNumInput value={g.sds} onChange={(v) => setGl("sds", v)} step={0.05} /></td></tr>
              <tr><td>R <span style={{ color: LT.faint, fontSize: 10 }}>(ref)</span></td><td style={{ textAlign: "right", fontFamily: MONO }}>{g.R}</td></tr>
              <tr><td style={{ paddingTop: 6 }}>E = 0.70 · V</td><td style={{ textAlign: "right", fontFamily: MONO, fontWeight: 700, paddingTop: 6 }}>{fmt(E_seis, 2)} lbs</td></tr>
            </tbody></table>
          </div>
          <div style={{ flex: "1 1 260px", border: `1px solid ${LT.rule}`, padding: "10px 14px" }}>
            <div style={{ fontSize: 11, fontWeight: 700, marginBottom: 8 }}>Wind</div>
            <table style={{ fontSize: 12, width: "100%" }}><tbody>
              <tr><td>W<sub>WIND</sub> (lbs)</td><td style={{ textAlign: "right" }}><LtNumInput value={g.wWind} onChange={(v) => setGl("wWind", v)} /></td></tr>
              <tr><td style={{ paddingTop: 6 }}>{g.code >= 3 ? "F = 0.60 · W" : "F = W"}</td><td style={{ textAlign: "right", fontFamily: MONO, fontWeight: 700, paddingTop: 6 }}>{fmt(F_wind)} lbs</td></tr>
            </tbody></table>
          </div>
          <div style={{ flex: "1 1 260px", border: `1px solid ${LT.rule}`, padding: "10px 14px" }}>
            <div style={{ fontSize: 11, fontWeight: 700, marginBottom: 8 }}>Dead loads</div>
            <table style={{ fontSize: 12, width: "100%" }}><tbody>
              <tr><td>Roof DL (psf)</td><td style={{ textAlign: "right" }}><LtNumInput value={g.roofDL} onChange={(v) => setGl("roofDL", v)} /></td></tr>
              <tr><td>Floor DL (psf)</td><td style={{ textAlign: "right" }}><LtNumInput value={g.floorDL} onChange={(v) => setGl("floorDL", v)} /></td></tr>
              <tr><td>Wall self (psf)</td><td style={{ textAlign: "right" }}><LtNumInput value={g.wallDL} onChange={(v) => setGl("wallDL", v)} /></td></tr>
            </tbody></table>
          </div>
          <div style={{ flex: "1 1 260px", border: `1px solid ${LT.rule}`, padding: "10px 14px" }}>
            <div style={{ fontSize: 11, fontWeight: 700, marginBottom: 8 }}>Sheathing</div>
            <table style={{ fontSize: 12, width: "100%" }}><tbody>
              <tr><td>Grade</td><td style={{ textAlign: "right" }}>
                <select value={g.grade === "str1" ? "str1" : "rated"} onChange={(e) => setGl("grade", e.target.value)} style={ltSel}>
                  <option value="rated">1/2&Prime; rated sheathing</option>
                  <option value="str1">1/2&Prime; Structural I</option>
                </select>
              </td></tr>
              <tr><td style={{ paddingTop: 6 }}>Type 1/2/3 wind (plf)</td><td style={{ textAlign: "right", fontFamily: MONO, paddingTop: 6 }}>{schedFor(g.grade).slice(0,3).map((t) => t.wind).join(" / ")}</td></tr>
              <tr><td>Type 1/2/3 seismic (plf)</td><td style={{ textAlign: "right", fontFamily: MONO }}>{schedFor(g.grade).slice(0,3).map((t) => t.seismic).join(" / ")}</td></tr>
            </tbody></table>
          </div>
        </div>
      </LtCollapse>

      <LtCollapse title={`Wall line elevation — total length ${fmt(totalL, 1)} ft`}>
        <LtElevation segments={segments} results={results} marks={marks} />
        <div style={{ fontSize: 10, color: LT.faint, marginTop: 4 }}>Click a wall to highlight its column in every table below.</div>
      </LtCollapse>

      <LtCollapse title="Wall segments — inputs">
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              {[
                ["length", "Length", "ft", 0.5],
                ["height", "Height", "ft", 0.5],
                ["roofTrib", "Roof trib.", "ft", 0.5],
                ["floorTrib", "Floor trib.", "ft", 0.5],
                ["hdDist", "HD dist. to end of wall", "in", 0.5],
              ].map(([key, label, unit, step]) => (
                <tr key={key} style={{ borderBottom: `1px solid ${LT.rule}` }}>
                  <td style={{ padding: "5px 10px", fontSize: 12, whiteSpace: "nowrap" }}>{label} <span style={{ color: LT.faint, fontSize: 11 }}>({unit})</span></td>
                  {segments.map((s, i) => (
                    <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                      <LtNumInput value={s[key]} onChange={(v) => setSeg(i, key, v)} step={step} width={58} />
                    </td>
                  ))}
                </tr>
              ))}
              <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
                <td style={{ padding: "5px 10px", fontSize: 12 }}>Wall thickness <span style={{ color: LT.faint, fontSize: 11 }}>(in)</span></td>
                {segments.map((s, i) => (
                  <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                    <select value={s.thickness} onChange={(e) => setSeg(i, "thickness", +e.target.value)} style={ltSel}>
                      <option value={3.5}>3.5</option><option value={5.5}>5.5</option><option value={7.25}>7.25</option>
                    </select>
                  </td>
                ))}
              </tr>
              <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
                <td style={{ padding: "5px 10px", fontSize: 12 }}>Anchored into</td>
                {segments.map((s, i) => (
                  <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                    <select value={s.anchor} onChange={(e) => setSeg(i, "anchor", e.target.value)} style={ltSel}>
                      <option>Concrete</option><option>Masonry</option><option>Wood</option>
                    </select>
                  </td>
                ))}
              </tr>
              <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
                <td style={{ padding: "5px 10px", fontSize: 12 }}>Selected shearwall type</td>
                {segments.map((s, i) => (
                  <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                    <select value={s.selType} onChange={(e) => setSeg(i, "selType", +e.target.value)} style={ltSel}>
                      <option value={1}>1</option><option value={2}>2</option><option value={3}>3</option>
                      <option value={4}>4 (2-sided)</option><option value={5}>5 (2-sided)</option><option value={6}>6 (2-sided)</option>
                    </select>
                  </td>
                ))}
              </tr>
              <LtRow label="Aspect ratio h/L" tip="SW Calc!E22 — NG! if h/L > 3.5" cells={results} render={(r) => <LtChip v={r.aspectNG ? "NG!" : r.aspect} d={2} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="Demand / capacity summary" badge={failBadge(anyFail.shear || anyFail.post || anyFail.hd)}>
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <LtRow label="Wind shear D/C" tip="vW ÷ schedule wind allowable at the selected type" cells={results} render={(r) => <LtUtilBar ratio={r.utilW} />} />
              <LtRow label="Seismic shear D/C" tip="vS ÷ (2w/l factor × schedule seismic allowable at the selected type)" cells={results} render={(r) => <LtUtilBar ratio={r.utilS} />} />
              <LtRow label="End post D/C" tip="max compression ÷ NDS capacity of the recommended post" cells={results} render={(r) => <LtUtilBar ratio={r.utilPost} />} />
              <LtRow label="Holdown D/C" tip="max uplift ÷ capacity of the recommended HDU" cells={results} render={(r) => (r.maxUplift === 0 ? <LtChip v="—" /> : <LtUtilBar ratio={r.utilHD} />)} />
              <LtRow label="Verdict" cells={results} render={(r) => <LtChip v={r.pass ? "OK" : "FAILED!!!"} />} />
            </tbody>
          </table>
        </div>
        <div style={{ fontSize: 10, color: LT.faint, marginTop: 4 }}>Bar fills toward the 100% marker. Green &lt; 85% · amber 85–100% · hatched red &gt; 100% (▲ over capacity).</div>
      </LtCollapse>

      <LtCollapse title="Seismic design" badge={failBadge(results.some((r) => r.active && r.sugS === "FAILED!!!"))} defaultOpen={false}>
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <LtRow label="F" unit="lbs" tip="E23: F = E · L / ΣL" cells={results} render={(r) => <LtChip v={r.Fs} d={2} />} />
              <LtRow label="Shear v" unit="plf" tip="E24: v = F / L" cells={results} render={(r) => <LtChip v={r.vS} d={2} />} />
              <LtRow label="Seismic factor 2w/l" tip="E25: aspect ≥ 2 → 2L/h, else 1" cells={results} render={(r) => <LtChip v={r.factor} d={2} />} />
              <LtRow label="Allowable shear" unit="plf" tip="E26" cells={results} render={(r) => <LtChip v={r.allowS} d={1} />} />
              <LtRow label="Suggested shearwall #" tip="E27" cells={results} render={(r) => <LtChip v={r.sugS} />} />
              <LtRow label="Mot" unit="ft·lbs" tip="E28: Mot = F · h" cells={results} render={(r) => <LtChip v={r.MotS} d={0} />} />
              <LtRow label="DL factor A = 1+0.14·SDS" tip="E29" cells={results} render={(r) => <LtChip v={r.A} d={2} />} />
              <LtRow label="A × wDL" unit="plf" tip="E30" cells={results} render={(r) => <LtChip v={r.AwDL} d={1} />} />
              <LtRow label="End post compression" unit="lbs" tip="E31" cells={results} render={(r) => <LtChip v={r.compS} d={0} />} />
              <LtRow label="DL factor B = 0.6−0.14·SDS" tip="E32" cells={results} render={(r) => <LtChip v={r.B} d={2} />} />
              <LtRow label="End post uplift, HDs" unit="lbs" tip="E34 — < 625 lbs → neglect" cells={results} render={(r) => <LtChip v={r.upHD_S} d={0} />} />
              <LtRow label="End post uplift, straps" unit="lbs" tip="E35" cells={results} render={(r) => <LtChip v={r.upStrap_S} d={0} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="Wind design" badge={failBadge(results.some((r) => r.active && r.sugW === "FAILED!!!"))} defaultOpen={false}>
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <LtRow label="F" unit="lbs" tip="E37: F = Fwind · L / ΣL" cells={results} render={(r) => <LtChip v={r.Fw} d={0} />} />
              <LtRow label="Shear v" unit="plf" tip="E38" cells={results} render={(r) => <LtChip v={r.vW} d={1} />} />
              <LtRow label="Suggested shearwall #" tip="E39" cells={results} render={(r) => <LtChip v={r.sugW} />} />
              <LtRow label="Mot" unit="ft·lbs" tip="E40" cells={results} render={(r) => <LtChip v={r.MotW} d={0} />} />
              <LtRow label="wDL" unit="plf" tip="E41" cells={results} render={(r) => <LtChip v={r.wdl} d={1} />} />
              <LtRow label="End post compression" unit="lbs" tip="E42 (source-sheet denominator replicated verbatim)" cells={results} render={(r) => <LtChip v={r.compW} d={0} />} />
              <LtRow label="End post uplift, HDs" unit="lbs" tip="E45" cells={results} render={(r) => <LtChip v={r.upHD_W} d={0} />} />
              <LtRow label="End post uplift, straps" unit="lbs" tip="E46" cells={results} render={(r) => <LtChip v={r.upStrap_W} d={0} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="End posts & holdowns" badge={failBadge(anyFail.post || anyFail.hd)}>
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <LtRow label="Max end post compression" unit="lbs" tip="E47" cells={results} render={(r) => <LtChip v={r.maxComp} d={0} />} />
              <LtRow label="Recommended minimum end post" tip="E48 — vs NDS column capacities" cells={results} render={(r) => <LtChip v={r.post} />} />
              <LtRow label="Max holdown uplift" unit="lbs" tip="E49" cells={results} render={(r) => <LtChip v={r.maxUplift === 0 ? "—" : r.maxUplift} d={0} />} />
              <LtRow label="Recommended HD holdown" tip="E50 — Simpson HDU; doubled when anchored to wood" cells={results} render={(r) => <LtChip v={r.hd} />} />
              <LtRow label="Anchored with" tip="E51/E52" cells={results} render={(r) => (
                <span style={{ fontFamily: MONO, fontSize: 12 }}>
                  {r.anchorSel === "None" ? <LtChip v="None" /> : <>
                    <LtChip v={r.anchorSel} />
                    <div style={{ fontSize: 10, color: LT.faint }}>{isNum(r.embed) ? `${r.embed}″ embed` : r.embed}</div>
                  </>}
                </span>
              )} />
              <LtRow label="If anchored at end of FDN wall" tip="E53/E54" cells={results} render={(r) => (
                <span style={{ fontFamily: MONO, fontSize: 12 }}>
                  {r.anchorEnd === "None" ? <LtChip v="None" /> : <>
                    <LtChip v={r.anchorEnd} />
                    <div style={{ fontSize: 10, color: LT.faint }}>{isNum(r.embedEnd) ? `${r.embedEnd}″ embed` : r.embedEnd}</div>
                  </>}
                </span>
              )} />
              <LtRow label="Max strap uplift" unit="lbs" tip="E55" cells={results} render={(r) => <LtChip v={r.maxStrap === 0 ? "—" : r.maxStrap} d={0} />} />
              <LtRow label="Alternate strap holdown" tip="E56" cells={results} render={(r) => <LtChip v={r.altStrap} />} />
              <LtRow label="Strap at FDN corner / end" tip="E57" cells={results} render={(r) => <LtChip v={r.strapCorner} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="Deflection & type check">
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <LtRow label="Δ seismic" unit="in" tip="Q2: bending + nail slip (Ga) + rotation terms" cells={results} render={(r) => <LtChip v={isFinite(r.deflS) ? r.deflS : "—"} d={3} />} />
              <LtRow label="Δ wind" unit="in" tip="Q3" cells={results} render={(r) => <LtChip v={isFinite(r.deflW) ? r.deflW : "—"} d={3} />} />
              <LtRow label="Selected type vs. required" tip="E59" cells={results} render={(r) => <LtChip v={r.status} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="Holdown footing estimate" defaultOpen={false}>
        <div className="sw-scroll">
          <table className="sw-table">
            <LtSegHeader segments={segments} marks={marks} />
            <tbody>
              <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
                <td style={{ padding: "5px 10px", fontSize: 12 }}>Footing width <span style={{ color: LT.faint, fontSize: 11 }}>(ft)</span></td>
                {segments.map((s, i) => (
                  <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                    <LtNumInput value={s.ftgWidth} onChange={(v) => setSeg(i, "ftgWidth", v)} step={0.01} width={58} />
                  </td>
                ))}
              </tr>
              <tr style={{ borderBottom: `1px solid ${LT.rule}` }}>
                <td style={{ padding: "5px 10px", fontSize: 12 }}>Footing thickness <span style={{ color: LT.faint, fontSize: 11 }}>(in)</span></td>
                {segments.map((s, i) => (
                  <td key={i} style={{ padding: "4px 8px", textAlign: "right" }}>
                    <LtNumInput value={s.ftgThick} onChange={(v) => setSeg(i, "ftgThick", v)} step={1} width={58} />
                  </td>
                ))}
              </tr>
              <LtRow label="Lmin, seismic" unit="ft" tip="E69 — quadratic bearing solve" cells={results} render={(r) => <LtChip v={isFinite(r.LminS) ? r.LminS : "—"} d={2} />} />
              <LtRow label="Lmin, wind" unit="ft" tip="E74" cells={results} render={(r) => <LtChip v={isFinite(r.LminW) ? r.LminW : "—"} d={2} />} />
              <LtRow label="Required footing length" unit="ft" tip="E62 = max(L+1, Lmin seismic, Lmin wind)" cells={results} render={(r) => <LtChip v={isFinite(r.reqFtgLen) ? r.reqFtgLen : "—"} d={2} />} />
            </tbody>
          </table>
        </div>
      </LtCollapse>

      <LtCollapse title="Shearwall schedule (reference)" defaultOpen={false}>
        <div className="sw-scroll">
          <table className="sw-table" style={{ fontSize: 11 }}>
            <thead>
              <tr style={{ borderBottom: `1.5px solid ${LT.ink}`, textAlign: "left" }}>
                {["MARK", "SHEATHING", "EDGE NAILING", "FIELD NAILING", "BOTTOM PLATE — CONCRETE", "BOTTOM PLATE — WOOD", "WIND (plf)", "SEISMIC (plf)", "Ga"].map((h) => (
                  <th key={h} style={{ padding: "4px 8px", fontSize: 10, letterSpacing: "0.06em" }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {schedFor(g.grade).map((t) => (
                <tr key={t.mark} style={{ borderBottom: `1px solid ${LT.rule}` }}>
                  <td style={{ padding: "5px 8px", fontFamily: MONO, fontWeight: 700, color: LT.blue }}>{t.mark}</td>
                  <td style={{ padding: "5px 8px" }}>{t.sheathing}</td>
                  <td style={{ padding: "5px 8px" }}>{t.edge}</td>
                  <td style={{ padding: "5px 8px" }}>{t.field}</td>
                  <td style={{ padding: "5px 8px" }}>{t.concrete}</td>
                  <td style={{ padding: "5px 8px" }}>{t.wood}</td>
                  <td style={{ padding: "5px 8px", fontFamily: MONO, textAlign: "right" }}>{t.wind}</td>
                  <td style={{ padding: "5px 8px", fontFamily: MONO, textAlign: "right" }}>{t.seismic}</td>
                  <td style={{ padding: "5px 8px", fontFamily: MONO, textAlign: "right" }}>{t.ga.toFixed(1)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </LtCollapse>
    </div>
  );
}

/* ════════════════════════════════════════════════════════════════════════
   DESIGN TAB — plan view fed by the Plan Sketcher
   Each point-load wall becomes a shear-wall LINE carrying its reaction
   (lbs) and wall height. Optimize fills every line; walls drag along
   their line with live recalc; right-click a wall to override holdown,
   edge nailing (type), or end post.
   ════════════════════════════════════════════════════════════════════════ */

// override validation against the engine's own capacities
const postAllowable = (r, t, name) => {
  const P = r.Pa;
  if (t <= 4) return name==="(2) 2x4" ? P.Pa224 : name==="4x4" ? P.Pa44 : name==="4x6" ? (P.Pa46*3.5)/5.5 : 0;
  return name==="(2) 2x6" ? P.Pa226 : name==="4x6" ? P.Pa46 : name==="6x6" ? P.Pa66 : name==="6x8" ? P.Pa68 : 0;
};
const hdCapacity = (name) => { const m = HD_TABLE.find(h => name.endsWith(h.name)); return m ? m.cap : 0; };

// evaluate one line's segments through the engine (auto type unless overridden)
function lineResults(line, segs, g, d) {
  const gL = { ...g, wWind: line.forceLbs, vSeismic: line.forceLbsSeismic || 0 };  // rev 62: per-line seismic demand (post-R reduced reaction, fed like wWind; engine envelopes W vs S)
  const totalL = segs.reduce((a, s) => a + s.length, 0);
  return segs.map((s) => {
    // (rev 49) DL tributary now rides on the LINE (per wall, per floor — set in runDesignHandoff from
    // wallProps), replacing the old global d.roofTrib/d.floorTrib. Only the INPUT SOURCE changed; the
    // engine's dead-load formula (calcCore.js: wdl = roofTrib·roofDL + floorTrib·floorDL + wallDL·h) is
    // byte-identical. ?? d.* keeps any pre-rev-49 / trib-less line working. Per-floor matters for stacked
    // walls: stackedLineResults runs floor 1 and floor 2 each through here with their own line.*.
    const base = { ...baseDesignSeg({ ...d, height: line.heightFt,
                     roofTrib:  line.roofTrib  ?? d.roofTrib,
                     floorTrib: line.floorTrib ?? d.floorTrib }), length: s.length };
    const r1 = calcSegment({ ...base, selType: 1 }, gL, totalL);
    let autoType = 1;
    if (r1.active && isNum(r1.sugS) && isNum(r1.sugW)) autoType = Math.max(r1.sugS, r1.sugW);
    const selType = s.ov && s.ov.type ? s.ov.type : Math.min(autoType, 6);
    const r = calcSegment({ ...base, selType }, gL, totalL);
    const ovBad = {
      type: s.ov && s.ov.type ? r.status !== "OK" : false,
      hd:   s.ov && s.ov.hd ? (s.ov.hd === "None" ? r.maxUplift !== 0 : r.maxUplift >= hdCapacity(s.ov.hd)) : false,
      post: s.ov && s.ov.post ? r.maxComp > postAllowable(r, d.thickness, s.ov.post) : false,
    };
    const dispHd   = s.ov && s.ov.hd   ? s.ov.hd   : r.hd;
    const dispPost = s.ov && s.ov.post ? s.ov.post : r.post;
    const failed = !r.active || r.status !== "OK" || r.aspectNG || r.post === "NG!" || r.hd === "NG!" || ovBad.type || ovBad.hd || ovBad.post;
    return { ...r, autoType: r1.active && (r1.sugS === "FAILED!!!" || r1.sugW === "FAILED!!!") ? "FAILED!!!" : r1.aspectNG ? "NG!" : autoType,
             selType, dispHd, dispPost, ovBad, failed };
  });
}

// ── Two-story vertical stacking (rev 27 / Step 6) ────────────────────────────
// At the 1st-floor base the overturning is ARM-AWARE: the roof reaction sits a
// full upper story higher, so its moment arm is H₁+H₂, not H₁. Because Step 5
// already handed each floor the correct force AND design height, the arm-aware
// base moment is exactly the SUM of the two floors' engine overturning moments
// for the same vertically-aligned segment:  M_base = Mot(1st) + Mot(2nd).
//   e.g. roof 5k @ 20ft + 2nd-floor 6k @ 10ft over a 10ft wall →
//        (5·20 + 6·10)/10 = 16k  (NOT a flat (5+6)=11k).
// End post + holdown are re-derived from that combined moment using the engine's
// OWN formula shapes — calcSegment / lineResults are never touched (the withUtil
// pattern). Shear capacity (status/selType/v) is unaffected: stacking changes
// only overturning, and the shear was already carried by Step 5's combined load.
// Step 7 (rev 28): the secondary detailing — anchor, embedment, strap, deflection
// and footing — is now ALSO re-derived from the stacked demand, by mirroring
// calcSegment's anchorFor / embedFor / strapFor / defl / footing formula shapes
// here (the engine's 7 guarded fns stay byte-identical). Deflection's shear v is
// unchanged (the 1st-floor story shear was already carried by Step 5's combined
// load); only its chord (bending) term uses the STACKED end post, so a stacked
// wall with a bigger required chord reports a smaller in-plane Δ — the as-built
// behavior.
// rev 63 (SANCTIONED guarded change — user-approved; stackSeg guard is now
// golden-OUTPUT, re-baselined): the UPPER-STORY dead load now stacks onto the
// 1st-floor base, because the 2nd-floor + roof gravity travels down through the
// 1st-floor end posts. It is added through EACH case's factored bucket — wind
// compression +r2.wdl, seismic compression +r2.AwDL (A=1+0.14·Sds); wind uplift
// +r2.CwDL (0.6·D), seismic uplift +r2.BwDL ((0.6−0.14·Sds)·D, E_v-consistent) —
// so it REDUCES net uplift (smaller holdowns) and RAISES post compression (the
// physically-correct two-way effect). The footing base-shear term is now CUMULATIVE
// (r1.F+r2.F) to match the summed moments. r2's factored buckets already exist on
// the 2nd-floor calcSegment result; r1.B==r2.B (shared Sds), so aF is unchanged.
const upliftStk = (Mot, w, L, denomIn) => {            // mirror of calcSegment's local upliftFn
  const u = (Mot - w*L*(L/2 - 1.5/12)) / (L - denomIn/12);
  return u < 0 ? 0 : u < 625 ? "neglect" : u;
};
function stackSeg(r1, r2, L, g, d, h) {
  if (!r1 || !r1.active || !r2 || !r2.active) return r1;   // top-floor / inactive → no stacking
  const sp = g.species === 1, SCHED = schedFor(g.grade);
  const anchor = d.anchor, hdDist = d.hdDist, thickness = d.thickness, ftgW = d.ftgWidth, ftgT = d.ftgThick;
  const isWood = anchor === "Wood";
  // ── ARM-AWARE combined overturning (= sum of the two floors' engine moments) ──
  const MotW = r1.MotW + r2.MotW;                          // arm-aware combined wind moment @ 1st-floor base
  const MotS = r1.MotS + r2.MotS;                          // …and seismic
  const minL = Math.min(3, L/2);
  const compW = (MotW + (r1.wdl  + r2.wdl ) * L * minL) / (L - (1.5 + hdDist/12) / 12);  // E42 quirk preserved · (rev 63) +upper-story DL onto the post
  const compS = (MotS + (r1.AwDL + r2.AwDL) * L * minL) / (L - (1.5 + hdDist)   / 12);   // (rev 63) +upper-story DL (seismic A=1+0.14·Sds bucket)
  const upHD_W = upliftStk(MotW, r1.CwDL + r2.CwDL, L, 1.5 + hdDist);   // (rev 63) +upper-story DL resists uplift (wind C=0.6·D bucket)
  const upHD_S = upliftStk(MotS, r1.BwDL + r2.BwDL, L, 1.5 + hdDist);   // (rev 63) +upper-story DL (seismic B=(0.6−0.14·Sds)·D bucket, E_v consistent)
  const upStrap_W = upliftStk(MotW, r1.CwDL + r2.CwDL, L, 3);        // E56/E57 strap uplift: denominator is 3", not 1.5+hdDist
  const upStrap_S = upliftStk(MotS, r1.BwDL + r2.BwDL, L, 3);
  const maxComp   = xMax(compS, compW);
  const maxUplift = xMax(upHD_S, upHD_W);
  const maxStrap  = xMax(upStrap_S, upStrap_W);
  // ── End post (engine's own ladder, same Pa as the 1st-floor segment) ──
  const P = r1.Pa;
  const post = thickness <= 4
    ? maxComp <= P.Pa224 ? "(2) 2x4" : maxComp <= P.Pa44 ? "4x4" : maxComp <= (P.Pa46*3.5)/5.5 ? "4x6" : "NG!"
    : maxComp <= P.Pa226 ? "(2) 2x6" : maxComp <= P.Pa46 ? "4x6" : maxComp <= P.Pa66 ? "6x6" : maxComp <= P.Pa68 ? "6x8" : "NG!";
  // ── Holdown (HD_TABLE lookup on the stacked uplift) ──
  let hd;
  if (maxUplift === 0) hd = "None";
  else { const found = HD_TABLE.find((x) => maxUplift < x.cap); hd = found ? (isWood ? `(2) ${found.name}` : found.name) : "NG!"; }
  // ── Anchor + embedment (mirror of calcSegment.anchorFor / embedFor on the stacked hd/uplift) ──
  const anchorFor = (variant) => {
    if (maxUplift === 0 || hd === "None") return "None";
    if (anchor === "Concrete") {
      if (hd === "HDU2") return maxUplift < 4780 ? "SSTB16" : "5/8'' A.B.";
      if (hd === "HDU4") return maxUplift < 4780 ? "SSTB16" : "5/8'' A.B.";
      if (hd === "HDU5") return maxUplift < 5175 ? "SSTB24" : "5/8'' A.B.";
      if (hd === "HDU8") return maxUplift < 10100 ? "SSTB28" : "7/8'' A.B.";
      return "1'' A.B.";
    }
    if (anchor === "Masonry") {
      const lim = variant === "interior" ? { a:4780, b:4780, c:6385 } : { a:1850, b:1850, c:4815 };
      if (hd === "HDU2" || hd === "HDU4") return maxUplift < lim.a ? "SSTB16" : "5/8'' A.B.";
      if (hd === "HDU5") return maxUplift < lim.b ? "SSTB24" : "5/8'' A.B.";
      if (hd === "HDU8") return maxUplift < lim.c ? "SSTB28" : "7/8'' A.B.";
      return "1'' A.B.";
    }
    if (["(2) HDU2", "(2) HDU4", "(2) HDU5"].includes(hd)) return "5/8'' Rod";
    if (hd === "(2) HDU8") return "7/8'' Rod";
    if (hd === "(2) HHDQ11" || hd === "(2) HHDQ14") return "1'' Rod";
    return "NG!!";
  };
  const anchorSel = anchorFor("interior");
  const anchorEnd = anchor === "Masonry" ? anchorFor("end") : anchorFor("interior");
  const embedFor = (anchorName, atEnd) => {
    if (anchorName === "None") return "None";
    if (["SSTB16","SSTB24","SSTB28"].includes(anchorName)) return "Simpson";
    if (anchor === "Concrete") return Math.max(16, Math.floor(maxUplift / (atEnd ? 876 : 1752) + 5));
    if (anchor === "Masonry") return Math.max(16, Math.floor(maxUplift / (atEnd ? 254 : 508) + 5));
    return "Threaded";
  };
  const embed = embedFor(anchorSel, false);
  const embedEnd = embedFor(anchorEnd, true);
  // ── Straps (mirror of calcSegment.strapFor on the stacked maxStrap/uplift) ──
  const strapFor = (lims) => {
    if (maxUplift === 0) return "None";
    if (anchor === "Concrete") { for (const [lim, name] of lims) if (maxStrap < lim) return name; return "None"; }
    if (anchor === "Wood") {
      const woodLims = [[2010,"MST37"],[3105,"MST48"],[4800,"MST60"],[5660,"MSTC78"],[9235,"CMST12"]];
      for (const [lim, name] of woodLims) if (maxStrap < lim) return name; return "None";
    }
    return "None";
  };
  const altStrap = strapFor([[3195,"STHD8"],[3730,"STHD10"],[5785,"STHD14"]]);
  const strapCorner = strapFor([[2370,"STHD8"],[3730,"STHD10"],[5025,"STHD14"]]);
  // ── Deflection (engine's defl shape; shear v unchanged, chord uses the STACKED post) ──
  const Epost = ["(2) 2x4","4x4","(2) 2x6","4x6"].includes(post) ? (sp ? 1400000 : 1600000) : (sp ? 1500000 : 1300000);
  const Apost = post === "(2) 2x4" ? 10.5 : post === "4x4" ? 12.25 : post === "(2) 2x6" ? 16.5 : post === "4x6" ? 19.25 : post === "6x6" ? 30.25 : 39.875;
  const Ga = SCHED[Math.max(0, Math.min(SCHED.length - 1, r1.selType - 1))].ga;  // marks 1–6; 4–6 carry 2× combined Ga
  const defl = (v) => (8*(v/0.7)*Math.pow(h,3))/(Epost*Apost*L) + ((v/0.7)*h)/(1000*Ga) + (h/L)*0.125;
  const deflS = defl(r1.vS);
  const deflW = defl(r1.vW);
  // ── Footing (engine's quad; stacked moments + uplifts, 1st-floor dead load + base shear) ──
  const quad = (qa, qb, qc) => { const disc = qb*qb - 4*qa*qc; if (disc < 0 || qa === 0) return NaN; return (-qb + Math.sqrt(disc)) / (2*qa); };
  const aF = (Math.min(0.6, r1.B) * 150 * ftgW * ftgT) / 24;   // footing self-weight (B factor only; r1.B==r2.B, no DL sum)
  const P65 = (MotS + (r1.BwDL+r2.BwDL)*L*(L/2 - hdDist/12)) / (L - (1.5 + hdDist)/12);   // (rev 63) +upper-story DL
  const uS = numOr0(upHD_S);
  const LminS = quad(aF, (P65-uS)/2, uS*(hdDist/12 - L/2) + P65*(1.5/12 - L/2) - ((r1.Fs+r2.Fs)*ftgT)/12);   // (rev 63) cumulative seismic base shear
  const P70 = (MotW + (r1.CwDL+r2.CwDL)*L*(L/2 - hdDist/12)) / (L - (1.5 + hdDist/12)/12);   // (rev 63) +upper-story DL
  const uW = numOr0(upHD_W);
  const LminW = quad(aF, (P70-uW)/2, uW*(hdDist/12 - L/2) + P70*(1.5/12 - L/2) - ((r1.Fw+r2.Fw)*ftgT)/12);   // (rev 63) cumulative wind base shear
  const reqFtgLen = xMax(L + 1, LminS, LminW);
  return { ...r1, MotW, MotS, compW, compS, upHD_W, upHD_S, upStrap_W, upStrap_S,
           maxComp, maxUplift, maxStrap, post, hd,
           anchorSel, anchorEnd, embed, embedEnd, altStrap, strapCorner,
           deflS, deflW, LminS, LminW, reqFtgLen, stacked:true };
}
// Stacks a 1st-floor line onto its vertically-aligned 2nd-floor line (same id, shared segments),
// then re-derives override validation + display + pass/fail from the stacked numbers.
function stackedLineResults(line1, line2, segs, g, d) {
  const r1arr = lineResults(line1, segs, g, d);
  const r2arr = lineResults(line2, segs, g, d);
  return r1arr.map((r1, i) => {
    const stk = stackSeg(r1, r2arr[i], segs[i].length, g, d, line1.heightFt);
    const s = segs[i];
    const ovBad = {
      type: s.ov && s.ov.type ? stk.status !== "OK" : false,   // shear unaffected by stacking
      hd:   s.ov && s.ov.hd ? (s.ov.hd === "None" ? stk.maxUplift !== 0 : stk.maxUplift >= hdCapacity(s.ov.hd)) : false,
      post: s.ov && s.ov.post ? stk.maxComp > postAllowable(stk, d.thickness, s.ov.post) : false,
    };
    const dispHd   = s.ov && s.ov.hd   ? s.ov.hd   : stk.hd;
    const dispPost = s.ov && s.ov.post ? s.ov.post : stk.post;
    const failed = !stk.active || stk.status !== "OK" || stk.aspectNG || stk.post === "NG!" || stk.hd === "NG!" || ovBad.type || ovBad.hd || ovBad.post;
    return { ...stk, dispHd, dispPost, ovBad, failed };
  });
}

// 1st-floor-CONTROLLED stacked optimizer (rev 47). A stacked wall shares ONE segment layout across
// both floors, so its length is governed by the heavier 1st-floor COMBINED (arm-aware) demand, not the
// lighter 2nd floor. This mirrors generateDesign's (N, Ls) search but scores every candidate through
// the SAME validators the Design tab displays — stackedLineResults (1st-floor combined) AND the 2nd
// floor's own lineResults — and BOUNDS every layout to the 2-story segment (cap = the shared
// reconciled extent). It returns the shortest passing layout, so when the 2nd floor alone would take
// 6 ft but the stacked holdown/post can't pass at 6 ft, it grows the wall (e.g. 10 ft, up to the
// segment) — and that one length is used on both floors. If nothing passes within the segment it
// returns null → the line reports FAIL (never spills past the 2-story segment). calcCore.js is
// untouched: this only composes its exported primitives (calcSegment/baseDesignSeg via lineResults).
// (rev 73) Snap shear-wall segments so each sits INSIDE a solid wall run, instead of defaulting into an
// opening between two collinear walls. PLACEMENT-only and engine-neutral: the structural calc reads a
// segment's LENGTH and the line's total segment length (lineResults/calcSegment), never its `start`, so
// re-positioning changes nothing about the design result. A segment already fully inside a run is left
// where the engine placed it (so a continuous wall keeps the engine's even spacing); only a segment that
// overlaps a gap is shifted to the nearest run that can host it, packed left→right so placements never
// overlap. `runs` are line-local [start,end] pairs (0 = the line's `a` end). The user can still freely
// drag any placed segment along or across the walls afterward — this only sets the INITIAL position.
function snapSegsToRuns(segs, runs, lineLen) {
  if (!Array.isArray(runs) || runs.length === 0) return segs;                  // no wall geometry → leave as-is
  const solid = runs.reduce((a, r) => a + Math.max(0, r[1] - r[0]), 0);
  if (solid >= lineLen - 1e-3) return segs;                                    // wall is continuous → nothing to snap
  const inRun = (st, len) => runs.some(([s, e]) => st >= s - 1e-3 && st + len <= e + 1e-3);
  let lastEnd = 0;
  return segs.map((seg) => {
    const Ls = seg.length;
    let start = seg.start;
    if (!inRun(start, Ls)) {
      let best = null;
      for (const [s, e] of runs) {
        if (e - s < Ls - 1e-3) continue;                                       // run too short to host this segment
        let p = Math.min(Math.max(seg.start, s), e - Ls);                      // closest spot in this run to the original
        p = Math.max(p, lastEnd);                                             // don't overlap an earlier-placed segment
        if (p + Ls > e + 1e-3) continue;                                       // can't fit after lastEnd within this run
        const dist = Math.abs(p - seg.start);
        if (!best || dist < best.dist) best = { p, dist };
      }
      if (best) start = best.p;                                                // no run can host it → keep engine's start
    } else {
      start = Math.max(start, lastEnd);                                        // already in a wall; just guard overlap
    }
    lastEnd = start + Ls;
    return { ...seg, start: +start.toFixed(2) };
  });
}

function generateStackedDesign(line1, line2, g, d) {
  const cap = Math.max(0, Math.min(line2.lengthFt, line1.lengthFt));   // 2-story-segment length bound
  const snap = Math.max(0.25, d.snap || 0.5);
  const maxN = Math.max(1, Math.min(6, Math.floor(d.maxSegments)));
  const rnd = (x) => Math.round(x * 4) / 4;
  const mkSegs = (N, Ls) => { const gap = (cap - N*Ls)/(N+1);
    return Array.from({ length:N }, (_,i)=>({ start: rnd(gap + i*(Ls+gap)), length: Ls })); };
  const evalC = (segs) => {
    const stk = stackedLineResults(line1, line2, segs, g, d);   // combined 1st-floor demand (governs)
    const top = lineResults(line2, segs, g, d);                 // 2nd floor's own shear / aspect
    const ok = stk.length > 0 && stk.every(r=>!r.failed) && top.every(r=>!r.failed);
    const T = xMax(...stk.map(r=>isNum(r.selType) ? r.selType : 0));
    return { ok, T };
  };
  const solutions = [];
  for (let N = 1; N <= maxN; N++) {
    const maxLs = Math.min(d.maxSegLen, cap / N);
    if (maxLs < d.minSegLen - 1e-9) continue;
    const start = Math.ceil(d.minSegLen / snap) * snap;
    for (let Ls = start; Ls <= maxLs + 1e-9; Ls = +(Ls + snap).toFixed(4)) {
      const segs = mkSegs(N, Ls);
      const ev = evalC(segs);
      if (ev.ok) { solutions.push({ N, Ls, total: N*Ls, T: ev.T, segs }); break; }
    }
  }
  if (!solutions.length) return null;
  solutions.sort((a, b) => d.objective === "nailing"
    ? a.T - b.T || a.total - b.total || a.N - b.N
    : a.total - b.total || a.N - b.N || a.T - b.T);
  const best = solutions[0];
  return { segs: best.segs.map(s=>({...s})), meta:{ type: best.T, N: best.N, Ls: best.Ls, total: best.total, stacked:true } };
}

// Shearwall schedule reference table — shown at the bottom of the Design tab
// (same data as the Calculation Sheet's reference section)
function SwScheduleRef({ grade }) {
  return (
    <LtCollapse title="Shearwall schedule (reference)">
      <div className="sw-scroll">
        <table className="sw-table" style={{ fontSize:11 }}>
          <thead>
            <tr style={{ borderBottom:`1.5px solid ${LT.ink}`, textAlign:"left" }}>
              {["MARK", "SHEATHING", "EDGE NAILING", "FIELD NAILING", "BOTTOM PLATE — CONCRETE", "BOTTOM PLATE — WOOD", "WIND (plf)", "SEISMIC (plf)", "Ga"].map((h) => (
                <th key={h} style={{ padding:"4px 8px", fontSize:10, letterSpacing:"0.06em" }}>{h}</th>
              ))}
            </tr>
          </thead>
          <tbody>
            {schedFor(grade).map((t) => (
              <tr key={t.mark} style={{ borderBottom:`1px solid ${LT.rule}` }}>
                <td style={{ padding:"5px 8px", fontFamily:MONO, fontWeight:700, color:LT.blue }}>{t.mark}</td>
                <td style={{ padding:"5px 8px" }}>{t.sheathing}</td>
                <td style={{ padding:"5px 8px" }}>{t.edge}</td>
                <td style={{ padding:"5px 8px" }}>{t.field}</td>
                <td style={{ padding:"5px 8px" }}>{t.concrete}</td>
                <td style={{ padding:"5px 8px" }}>{t.wood}</td>
                <td style={{ padding:"5px 8px", fontFamily:MONO, textAlign:"right" }}>{t.wind}</td>
                <td style={{ padding:"5px 8px", fontFamily:MONO, textAlign:"right" }}>{t.seismic}</td>
                <td style={{ padding:"5px 8px", fontFamily:MONO, textAlign:"right" }}>{t.ga.toFixed(1)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <div style={{ fontSize:10, color:LT.faint, marginTop:4 }}>"Type n" on the plan and in the results table refers to MARK n in this schedule.</div>
    </LtCollapse>
  );
}

// Wall mark letters: A..Z, AA, AB, … assigned in line order then segment order
const letterOf = (k) => { let s = ""; k += 1; while (k > 0) { k -= 1; s = String.fromCharCode(65 + (k % 26)) + s; k = Math.floor(k / 26); } return s; };

// rev 62 — per-element GOVERNING CASE (Wind vs Seismic), pure display derivation. The engine already
// envelopes both cases per element (calcSegment: type=max(sugS,sugW); maxComp/maxUplift/reqFtgLen via
// xMax). These helpers just read which case drove each element so the Design table can tag it. They
// touch NO guarded fn — same out-of-engine pattern as withUtil. Return "W"/"S" or null (neither acts).
const _govShearCase = (r, grade) => {
  if (!r || !isNum(r.selType)) return null;
  const t = schedFor(grade)[Math.max(0, Math.min(5, r.selType - 1))];
  const uW = t.wind ? r.vW / t.wind : 0;
  const uS = (r.factor * t.seismic) ? r.vS / (r.factor * t.seismic) : 0;
  if (uW <= 0 && uS <= 0) return null;
  return uS > uW ? "S" : "W";
};
const _govBy = (s, w) => {            // larger demand governs; both ≤0 → no tag ("neglect"/non-numbers → 0)
  const ns = isNum(s) ? s : 0, nw = isNum(w) ? w : 0;
  if (ns <= 0 && nw <= 0) return null;
  return ns > nw ? "S" : "W";
};
function CaseTag({ which }) {
  if (!which) return null;
  const seis = which === "S";
  return (
    <span title={seis ? "Seismic governs this element" : "Wind governs this element"}
      style={{ display:"inline-block", marginLeft:6, verticalAlign:"middle", fontFamily:MONO, fontSize:10.5,
               fontWeight:700, lineHeight:1, padding:"2px 4px", borderRadius:3,
               color: seis ? SW.amber : SW.accent,
               background: seis ? SW.amberSoft : SW.accentSoft,
               border:`1px solid ${seis ? SW.amber : SW.accent}` }}>{which}</span>
  );
}

// ---------- the plan canvas ----------
function DesignPlan({ shape, lines, segsByLine, setSegsByLine, resultsByLine, selLine, setSelLine, snap, maxSegLen, onCtx, marks, showTags, lineNames }) {
  const svgRef = useRef(null);
  const dragRef = useRef(null);
  // fit viewBox to footprint
  const vb = useMemo(() => {
    let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
    (shape&&shape.nodes||[]).forEach(p=>{ x0=Math.min(x0,p.x);y0=Math.min(y0,p.y);x1=Math.max(x1,p.x);y1=Math.max(y1,p.y); });
    if(!(x1>x0)) { x0=0;y0=0;x1=100;y1=60; }
    const m=14; return { x:x0-m, y:y0-m, w:(x1-x0)+2*m, h:(y1-y0)+2*m };
  }, [shape]);
  const S = Math.max(vb.w, vb.h) / 110;   // graphic scale (matches sketcher's S idiom)
  const band = 1.2*S;                      // shear-wall band half-width (rev 13: halved — thin-band drafting symbol)
  // (rev 54/55) when a line is SELECTED in the Design tab, only its dashed CENTERLINE turns yellow as
  // an immediate "this is the selected wall" indicator. The shear-wall band keeps its pass/fail blue/red
  // so selection never masks a red FAIL.
  const SEL_STROKE = "#B8860B";            // selection gold/yellow — readable on the white plan

  const lineGeom = (ln) => {
    const ux=(ln.b.x-ln.a.x)/ln.lengthFt, uy=(ln.b.y-ln.a.y)/ln.lengthFt;     // along the line
    const nx=-uy, ny=ux;                                                       // across the line
    return { ux, uy, nx, ny };
  };
  const snapTo = (v) => Math.round(v / snap) * snap;
  const toPlan = (e) => {
    const r = svgRef.current.getBoundingClientRect();
    return { x: vb.x + ((e.clientX - r.left)/r.width)*vb.w, y: vb.y + ((e.clientY - r.top)/r.height)*vb.h };
  };

  const onDown = (e, lineId, idx, mode) => {
    if (e.button !== 0) return;
    e.preventDefault(); e.stopPropagation();
    e.currentTarget.setPointerCapture?.(e.pointerId);
    setSelLine(lineId);
    dragRef.current = { lineId, idx, mode, startPlan: toPlan(e), orig: { ...segsByLine[lineId][idx] } };
  };
  const onMove = (e) => {
    const dr = dragRef.current; if (!dr || !svgRef.current) return;
    const ln = lines.find(l => l.id === dr.lineId); if (!ln) return;
    const { ux, uy } = lineGeom(ln);
    const p = toPlan(e);
    const dxFt = (p.x - dr.startPlan.x)*ux + (p.y - dr.startPlan.y)*uy;        // movement along the line
    const segs = segsByLine[dr.lineId];
    const { idx, mode, orig } = dr;
    const prevEnd = idx > 0 ? segs[idx-1].start + segs[idx-1].length : 0;
    const nextStart = idx < segs.length-1 ? segs[idx+1].start : ln.lengthFt;
    let { start, length } = orig;
    if (mode === "M") {
      start = snapTo(Math.min(Math.max(orig.start + dxFt, prevEnd), nextStart - orig.length));
    } else if (mode === "R") {
      const end = snapTo(Math.min(Math.max(orig.start + orig.length + dxFt, orig.start + 1), Math.min(nextStart, orig.start + maxSegLen)));
      length = end - orig.start;
    } else if (mode === "L") {
      const ns = snapTo(Math.min(Math.max(orig.start + dxFt, Math.max(prevEnd, orig.start + orig.length - maxSegLen)), orig.start + orig.length - 1));
      start = ns; length = orig.start + orig.length - ns;
    }
    setSegsByLine(prev => ({ ...prev, [dr.lineId]: prev[dr.lineId].map((s, j) => j === idx ? { ...s, start, length } : s) }));
  };
  const onUp = () => { dragRef.current = null; };

  return (
    <svg ref={svgRef} viewBox={`${vb.x} ${vb.y} ${vb.w} ${vb.h}`}
         style={{ width:"100%", display:"block", background:C_BG, border:`1px solid ${SW.rule}`, borderRadius:8,
                  touchAction:"none", userSelect:"none", maxHeight:520 }}
         onPointerMove={onMove} onPointerUp={onUp} onPointerLeave={onUp}
         onContextMenu={(e)=>e.preventDefault()}>
      {/* footprint walls — no nodes (design view, not an editor) */}
      {(shape&&shape.edges||[]).map((ed,i)=>{
        const a=shape.nodes.find(n=>n.id===ed.a), b=shape.nodes.find(n=>n.id===ed.b);
        if(!a||!b) return null;
        return <line key={i} x1={a.x} y1={a.y} x2={b.x} y2={b.y} stroke={SW.wall} strokeWidth={0.55*S} strokeLinecap="round" opacity="0.8"/>;
      })}
      {/* design lines + shear walls */}
      {lines.map(ln=>{
        const { ux, uy, nx, ny } = lineGeom(ln);
        const segs = segsByLine[ln.id] || [];
        const res  = resultsByLine[ln.id] || [];
        const isSel = selLine === ln.id;
        const at = (ft, off=0) => ({ x: ln.a.x + ux*ft + nx*off, y: ln.a.y + uy*ft + ny*off });
        const vert = ln.o === "v";
        return (
          <g key={ln.id}>
            {/* line highlight (click selects) — force/length shown in the chips below the plan */}
            <line x1={ln.a.x} y1={ln.a.y} x2={ln.b.x} y2={ln.b.y}
                  stroke={isSel ? SEL_STROKE : SW.faint} strokeWidth={(isSel?0.5:0.3)*S}
                  strokeDasharray={`${1.6*S} ${1.2*S}`} opacity={isSel?0.9:0.45}
                  style={{cursor:"pointer"}} onClick={()=>setSelLine(ln.id)}/>
            {/* (rev 72) GRID BUBBLE at the line's `a` end — `a` is the min-coordinate end, i.e. the TOP
                for a vertical (N–S) line and the LEFT for a horizontal (E–W) line, so numbers land on
                top and letters on the left exactly like a plan grid. The bubble sits BEYOND the end
                along −(ux,uy) on an extension line; the label is always upright (no rotation). Black
                on white so it reads as drawing annotation, distinct from the blue/red wall callouts.
                (rev 73) the extension `stem` was lengthened ~4× (1.1→4.4·S) so the bubble sits well
                clear of the structural footprint — for the horizontal A/B lines this lifts the bubble
                completely off the corner wall-joints and outside the plan boundary. */}
            {(()=>{
              const rB=2.4*S, stem=4.4*S, gap=0.25*S, near={x:ln.a.x-ux*gap,y:ln.a.y-uy*gap};
              const cx=ln.a.x-ux*(stem+rB), cy=ln.a.y-uy*(stem+rB);
              return (
                <g pointerEvents="none">
                  <line x1={near.x} y1={near.y} x2={cx+ux*rB} y2={cy+uy*rB} stroke={SW.ink} strokeWidth={0.16*S}/>
                  <circle cx={cx} cy={cy} r={rB} fill={C_BG} stroke={SW.ink} strokeWidth={0.22*S}/>
                  <text x={cx} y={cy} textAnchor="middle" dominantBaseline="central"
                        fontSize={2.0*S} fontWeight="800" fill={SW.ink} fontFamily={MONO}>{lineNames[ln.id]}</text>
                </g>
              );
            })()}
            {/* shear-wall segments — distinct hatched band over the wall line */}
            {segs.map((s,i)=>{
              const r=res[i]||{};
              // (rev 55) shear-wall band keeps its PASS/FAIL color (blue/red) even when selected — only
              // the dashed centerline turns yellow (below), so selection never masks a red FAIL.
              const stroke = r.failed ? SW.red : SW.accent;
              const fill   = r.failed ? SW.redSoft : SW.accentSoft;
              const p0=at(s.start), p1=at(s.start+s.length);
              const corners=[ at(s.start,-band), at(s.start+s.length,-band), at(s.start+s.length,band), at(s.start,band) ];
              const mid = s.start + s.length/2;
              const hdRaw = (r.dispHd && r.dispHd!=="None") ? String(r.dispHd) : null;   // holdown designation, e.g. "HDU4" / "(2) HDU4" / "NG!"
              const hdNum = hdRaw ? (hdRaw.match(/HDU(\d+)/)?.[1] ?? "!") : null;         // the hold-down NUMBER shown in the dot bubble
              const hatch=[]; const step=1.3*S;
              for(let f=step; f<s.length; f+=step) hatch.push(f);
              return (
                <g key={i}
                   onContextMenu={(e)=>{ e.preventDefault(); e.stopPropagation(); onCtx(e, ln.id, i); }}>
                  {/* body — hatched band (color scheme preserved), drag to slide */}
                  <polygon points={corners.map(c=>`${c.x},${c.y}`).join(" ")}
                           fill={fill} stroke={stroke} strokeWidth={0.28*S}
                           style={{cursor:"grab"}} onPointerDown={(e)=>onDown(e,ln.id,i,"M")}/>
                  {hatch.map((f,k)=>{
                    const h1=at(s.start+Math.max(0,f-step*0.7), band), h2=at(s.start+f, -band);
                    return <line key={k} x1={h1.x} y1={h1.y} x2={h2.x} y2={h2.y} stroke={stroke} strokeWidth={0.12*S} opacity="0.5" pointerEvents="none"/>;
                  })}
                  {/* detail-bubble callout above wall center: ▽ holds the shear-wall TYPE, LENGTH is dimensioned above it */}
                  {(()=>{
                    const tipOff=band+1.3*S, triH=2.3*S, triHalf=1.35*S;
                    const apex=at(mid,-tipOff), tl=at(mid-triHalf,-(tipOff+triH)), trr=at(mid+triHalf,-(tipOff+triH));
                    const wallTop=at(mid,-band), typePt=at(mid,-(tipOff+triH*0.56)), lenPt=at(mid,-(tipOff+triH+1.05*S));
                    const rot=(pt)=> vert?`rotate(-90,${pt.x},${pt.y})`:undefined;
                    return (
                      <g pointerEvents="none">
                        <line x1={wallTop.x} y1={wallTop.y} x2={apex.x} y2={apex.y} stroke={stroke} strokeWidth={0.14*S}/>
                        <polygon points={`${apex.x},${apex.y} ${tl.x},${tl.y} ${trr.x},${trr.y}`} fill={C_BG} stroke={stroke} strokeWidth={0.16*S}/>
                        <text x={typePt.x} y={typePt.y} textAnchor="middle" dominantBaseline="central"
                              fontSize={1.5*S} fontWeight="800" fill={stroke} fontFamily={MONO} transform={rot(typePt)}>
                          {isNum(r.selType) ? r.selType : "—"}
                        </text>
                        <text x={lenPt.x} y={lenPt.y} textAnchor="middle" dominantBaseline="central"
                              fontSize={1.15*S} fontWeight="600" fill={SW.ink} fontFamily={MONO} transform={rot(lenPt)}>
                          {fmt(s.length,2)}′
                        </text>
                      </g>
                    );
                  })()}
                  {/* end zones — boundary X-box + holdown dot bubble carrying the HD number (dot kept; now numbered) */}
                  {[p0,p1].map((p,k)=>{
                    const eb=band, rot = vert?`rotate(-90,${p.x},${p.y})`:undefined;
                    return (
                      <g key={k} pointerEvents="none">
                        <rect x={p.x-eb} y={p.y-eb} width={2*eb} height={2*eb} fill={C_BG} stroke={stroke} strokeWidth={0.16*S}/>
                        <line x1={p.x-eb} y1={p.y-eb} x2={p.x+eb} y2={p.y+eb} stroke={stroke} strokeWidth={0.14*S}/>
                        <line x1={p.x-eb} y1={p.y+eb} x2={p.x+eb} y2={p.y-eb} stroke={stroke} strokeWidth={0.14*S}/>
                        {hdNum && <>
                          <circle cx={p.x} cy={p.y} r={0.92*S} fill={stroke} stroke={C_BG} strokeWidth={0.12*S}/>
                          <text x={p.x} y={p.y} textAnchor="middle" dominantBaseline="central"
                                fontSize={hdNum.length>1?0.92*S:1.15*S} fontWeight="700" fill={C_BG} fontFamily={MONO} transform={rot}>
                            {hdNum}
                          </text>
                        </>}
                      </g>
                    );
                  })}
                  {/* end stretch handles — invisible hit area (the X-box is the visual) */}
                  {[["L",p0],["R",p1]].map(([mode,p])=>(
                    <circle key={mode} cx={p.x} cy={p.y} r={1.5*S} fill="transparent"
                            style={{cursor:"ew-resize"}} onPointerDown={(e)=>onDown(e,ln.id,i,mode)}/>
                  ))}
                  {/* optional SW mark tag — gated by the "wall tags" toggle (off by default) */}
                  {showTags && (()=>{ const tg=at(mid, band+1.5*S); return (
                    <text x={tg.x} y={tg.y} textAnchor="middle" dominantBaseline="central"
                          fontSize={1.2*S} fontWeight="700" fill={stroke} fontFamily={MONO} pointerEvents="none"
                          transform={vert?`rotate(-90,${tg.x},${tg.y})`:undefined}>
                      SW-{(marks && marks[ln.id + "|" + i]) || "?"}
                    </text>
                  );})()}
                </g>
              );
            })}
          </g>
        );
      })}
      <text x={vb.x+2*S} y={vb.y+3*S} fontSize={1.4*S} fill={SW.faint} fontFamily={MONO}>
        PLAN — drag wall to slide · drag ▭ handles to stretch · right-click to edit · click a line to select
      </text>
    </svg>
  );
}

// ---------- right-click override menu for a shear wall ----------
function SwCtxMenu({ ctx, lines, segsByLine, resultsByLine, setOv, onRemove, onClose, thickness }) {
  if (!ctx) return null;
  const segs = segsByLine[ctx.lineId]||[]; const s = segs[ctx.idx]; if (!s) return null;
  const r = (resultsByLine[ctx.lineId]||[])[ctx.idx] || {};
  const postOpts = thickness <= 4 ? ["(2) 2x4","4x4","4x6"] : ["(2) 2x6","4x6","6x6","6x8"];
  const row = { display:"flex", justifyContent:"space-between", alignItems:"center", gap:10, padding:"4px 0", fontSize:12, color:SW.ink };
  const badge = (bad) => bad ? <span style={{color:SW.red,fontWeight:700,fontSize:11}}>NG</span> : null;
  return (
    <div style={{ position:"fixed", left:ctx.px, top:ctx.py, zIndex:60, background:SW.panel, border:`1px solid ${SW.rule}`,
                  borderRadius:8, padding:"10px 12px", minWidth:240, boxShadow:"0 12px 32px -8px rgba(28,39,51,0.28)" }}
         onContextMenu={(e)=>e.preventDefault()}>
      <div style={{ fontSize:11, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase", color:SW.accent, marginBottom:6 }}>
        Shear wall · {fmt(s.length,2)}′
      </div>
      <div style={row}>
        <span>Edge nailing (type)</span>
        <span style={{display:"flex",alignItems:"center",gap:6}}>
          {badge(r.ovBad&&r.ovBad.type)}
          <select style={selStyle} value={s.ov&&s.ov.type||0}
                  onChange={(e)=>setOv(ctx.lineId,ctx.idx,"type",+e.target.value||null)}>
            <option value={0}>Auto (T{isNum(r.autoType)?r.autoType:"—"})</option>
            <option value={1}>T1 · 6″ o.c.</option><option value={2}>T2 · 4″ o.c.</option><option value={3}>T3 · 3″ o.c.</option>
          </select>
        </span>
      </div>
      <div style={row}>
        <span>Holdown</span>
        <span style={{display:"flex",alignItems:"center",gap:6}}>
          {badge(r.ovBad&&r.ovBad.hd)}
          <select style={selStyle} value={s.ov&&s.ov.hd||""}
                  onChange={(e)=>setOv(ctx.lineId,ctx.idx,"hd",e.target.value||null)}>
            <option value="">Auto ({r.hd||"—"})</option>
            <option value="None">None</option>
            {HD_TABLE.map(h=><option key={h.name} value={h.name}>{h.name} · {fmt(h.cap)} lbs</option>)}
          </select>
        </span>
      </div>
      <div style={row}>
        <span>End post</span>
        <span style={{display:"flex",alignItems:"center",gap:6}}>
          {badge(r.ovBad&&r.ovBad.post)}
          <select style={selStyle} value={s.ov&&s.ov.post||""}
                  onChange={(e)=>setOv(ctx.lineId,ctx.idx,"post",e.target.value||null)}>
            <option value="">Auto ({r.post||"—"})</option>
            {postOpts.map(p=><option key={p} value={p}>{p}</option>)}
          </select>
        </span>
      </div>
      <div style={{ display:"flex", gap:8, marginTop:8 }}>
        <button style={{...swBtn(false), padding:"5px 10px"}} onClick={()=>{ setOv(ctx.lineId,ctx.idx,null,null); }}>Reset to auto</button>
        <button style={{...swBtn(false), padding:"5px 10px", color:SW.red, borderColor:SW.red}} onClick={()=>{ onRemove(ctx.lineId,ctx.idx); onClose(); }}>Remove wall</button>
        <button style={{...swBtn(true), padding:"5px 10px", marginLeft:"auto"}} onClick={onClose}>Done</button>
      </div>
    </div>
  );
}

// ---------- DESIGN TAB ----------
function DesignTab({ g, setGl, shape, lines, linesByFloor, segsByLine, setSegsByLine, ovSet, d, setDk, applyToCalc, selLine, setSelLine, twoStory, activeFloor, setActiveFloor, stale, onRebuild, calcPush, optimizePush, setOptimizePush, wTotal }) {
  const [ctx, setCtx] = useState(null);
  const [genMsg, setGenMsg] = useState(null);
  const [showTags, setShowTags] = useState(false);   // rev 13: SW marks no longer auto-show on the plan
  useEffect(()=>{ if(lines.length && !lines.find(l=>l.id===selLine)) setSelLine(lines[0].id); },[lines]); // eslint-disable-line

  const resultsByLine = useMemo(()=>{
    const out={};
    // 2-story mode, viewing the 1st floor: re-derive each line's end-post/holdown from the
    // ARM-AWARE combined overturning of both stories (roof reaction acts at H₁+H₂). The
    // matching 2nd-floor line shares this line's id (ax|key) and its segments (shared layout).
    const upper = (twoStory && activeFloor===1 && linesByFloor && linesByFloor[2]) ? linesByFloor[2] : null;
    lines.forEach(ln=>{
      const segs = segsByLine[ln.id]||[];
      const ln2 = upper && upper.find(L=>L.id===ln.id);
      out[ln.id] = ln2 ? stackedLineResults(ln, ln2, segs, g, d) : lineResults(ln, segs, g, d);
    });
    return out;
  },[lines, linesByFloor, segsByLine, g, d, twoStory, activeFloor]);
  const stacking = !!(twoStory && activeFloor===1 && linesByFloor && linesByFloor[2]);  // drives the 1st-floor overturning note

  // unique wall marks (SW-A, SW-B, …) in line order then segment order
  const wallMarks = useMemo(()=>{
    const m={}; let k=0;
    lines.forEach(ln=>{ (segsByLine[ln.id]||[]).forEach((s,i)=>{ m[ln.id+"|"+i]=letterOf(k); k++; }); });
    return m;
  },[lines, segsByLine]);

  // (rev 72) Per-line display name follows the standard structural GRID convention — no direction
  // prefix. N–S (vertical, windAxis "v") lines are NUMBERED 1,2,3… ordered left→right by x; E–W
  // (horizontal, windAxis "h") lines are LETTERED A,B,C… ordered top→bottom by y (screen y grows
  // downward, so ascending y = top→bottom). Positional like the SW marks — it tracks each line's
  // place in THIS floor's grid, not a persisted id. This name titles the matching Calculation-Sheet
  // sub-tab (via lineLabel → applyToCalc), so the Design and Calc tabs identify a wall identically.
  const lineNames = useMemo(()=>{
    const m={};
    const ns = lines.filter(l=>l.windAxis==="v").slice().sort((p,q)=> p.a.x-q.a.x || p.a.y-q.a.y);
    const ew = lines.filter(l=>l.windAxis==="h").slice().sort((p,q)=> p.a.y-q.a.y || p.a.x-q.a.x);
    ns.forEach((l,i)=>{ m[l.id]=String(i+1); });          // N–S → 1, 2, 3 …
    ew.forEach((l,i)=>{ m[l.id]=colName(i+1); });         // E–W → A, B, C …
    return m;
  },[lines]);
  const lineLabel = (ln) => `${lineNames[ln.id]} · ${fmt(ln.forceLbs/1000,2)}k · ${fmt(ln.lengthFt,0)}′`;

  const optimizeAll = () => {
    // Design EVERY wall across BOTH floors and MERGE onto the existing layouts (never wipe another
    // floor's lines — rev 46). A wall that exists on BOTH floors (same id) is a STACKED wall: its one
    // shared layout is governed by the heavier 1st-floor COMBINED demand, so it goes through
    // generateStackedDesign (1st floor controls; the chosen length is reused on the 2nd floor, bounded
    // by the 2-story segment — rev 47). A wall on only one floor (a 1-story wall, or a single-story
    // building) keeps the standalone generateDesign on its own reaction/length/height.
    const f1 = (linesByFloor && linesByFloor[1]) || (twoStory ? [] : lines);
    const f2 = (twoStory && linesByFloor && linesByFloor[2]) || [];
    const lower = new Map(f1.map(l=>[l.id,l]));
    const upper = new Map(f2.map(l=>[l.id,l]));
    const ids = new Set([...lower.keys(), ...upper.keys()]);
    const next = { ...segsByLine };            // merge — never drop another floor's lines
    let okCount=0, failNames=[]; const total = ids.size;
    ids.forEach(id=>{
      const l1 = lower.get(id), l2 = upper.get(id);
      let out, label;
      if(l1 && l2){                            // stacked → 1st-floor-controlled, segment-bounded
        out = generateStackedDesign(l1, l2, g, d);
        label = `${fmt(l1.forceLbs/1000,1)}k/${fmt(Math.min(l1.lengthFt,l2.lengthFt),0)}′ stacked line`;
      } else {                                 // 1-story-only / single-story → standalone
        const ln = l1 || l2;
        out = generateDesign({ ...g, wWind: ln.forceLbs, vSeismic: ln.forceLbsSeismic || 0 }, { ...d, lineLength: ln.lengthFt, height: ln.heightFt,
                               roofTrib: ln.roofTrib ?? d.roofTrib, floorTrib: ln.floorTrib ?? d.floorTrib });  // (rev 49) per-wall trib · (rev 62) per-line seismic
        label = `${fmt(ln.forceLbs/1000,1)}k/${fmt(ln.lengthFt,0)}′ line`;
      }
      if(out){ const sl=l1||l2; next[id]=snapSegsToRuns(out.segs, sl.runs, sl.lengthFt).map(s=>({...s})); okCount++; }   // rev 73: default-place inside a wall, not a gap
      else { next[id]=[]; failNames.push(label); }
    });
    setSegsByLine(next);
    setOptimizePush && setOptimizePush(optimizeSig(linesByFloor, lines, twoStory, g, d));   // rev 130b: remember the inputs this Optimize ran on
    setGenMsg(failNames.length
      ? { ok:false, text:`Optimized ${okCount}/${total} lines. No passing configuration for: ${failNames.join(", ")} — relax max segment length/count or allow type 3.` }
      : { ok:true, text:`Optimized all ${total} line${total>1?"s":""}.` });
  };

  const setOv = (lineId, idx, key, val) => ovSet(lineId, idx, key, val);
  const removeSeg = (lineId, idx) => setSegsByLine(prev => ({ ...prev, [lineId]: prev[lineId].filter((_,j)=>j!==idx) }));
  const addSeg = (lineId) => {
    const ln=lines.find(l=>l.id===lineId); if(!ln) return;
    const segs=(segsByLine[lineId]||[]).slice().sort((a,b)=>a.start-b.start);
    // largest gap on the line
    let best={start:0,room:0}, cursor=0;
    [...segs,{start:ln.lengthFt,length:0}].forEach(s=>{ const room=s.start-cursor; if(room>best.room) best={start:cursor,room}; cursor=Math.max(cursor,s.start+s.length); });
    if(best.room < d.minSegLen) return;
    const Ls=d.minSegLen;
    let st=+(best.start+(best.room-Ls)/2).toFixed(2);
    // (rev 73) snap the new segment into a SOLID wall run if the largest inter-segment gap lands in a
    // wall opening — choosing the nearest run that can host it without overlapping an existing segment.
    const runs=ln.runs;
    if(Array.isArray(runs) && runs.length){
      const inRun=(p)=>runs.some(([s,e])=> p>=s-1e-3 && p+Ls<=e+1e-3);
      if(!inRun(st)){
        let bp=null;
        for(const [s,e] of runs){ if(e-s<Ls-1e-3) continue;
          const p=Math.min(Math.max(st,s), e-Ls);
          if(p+Ls>e+1e-3) continue;
          if(segs.some(o=> p < o.start+o.length-1e-3 && p+Ls > o.start+1e-3)) continue;   // would overlap an existing seg
          const dist=Math.abs(p-st); if(!bp||dist<bp.dist) bp={p,dist};
        }
        if(bp) st=+bp.p.toFixed(2);
      }
    }
    setSegsByLine(prev=>({ ...prev, [lineId]: [...(prev[lineId]||[]), {start:st, length:Ls}].sort((a,b)=>a.start-b.start) }));
  };

  const sel = lines.find(l=>l.id===selLine);
  const selSegs = sel ? (segsByLine[sel.id]||[]) : [];
  const selRes  = sel ? (resultsByLine[sel.id]||[]) : [];
  // rev 130: the "Send line to calculation sheet" button goes red when the line CURRENTLY in the
  // sheet (calcPush.lineId) is the one selected AND its pushable data has changed since it was sent.
  // Selecting a DIFFERENT line is not "stale" — that's a fresh push, so the button stays normal.
  const calcStaleHint = !!(calcPush && sel && calcPush.lineId === sel.id && calcPush.sig !== calcPushSig(sel, selSegs, selRes, d));
  // rev 130b: the ⚡ Optimize design button produces the tab's design output; it goes red when an input
  // it consumes (any line's force/height/length/trib across both floors, or g / d) has changed since the
  // last Optimize. optimizePush is null until the first Optimize (so it's only red AFTER you've optimized).
  const optimizeLiveSig = optimizeSig(linesByFloor, lines, twoStory, g, d);
  const optimizeStaleHint = optimizePush != null && optimizePush !== optimizeLiveSig;
  const allPass = lines.length>0 && lines.every(ln=>{
    const rs=resultsByLine[ln.id]||[]; return rs.length>0 && rs.every(r=>!r.failed);
  });

  // rev 24: shown when a loaded file had geometry-less lines (excluded on load). The saved plan is
  // intact, so one click rebuilds every line from it. Rendered at the top of BOTH return paths below.
  const staleBanner = stale ? (
    <div style={{ marginTop:12, marginBottom:4, padding:"10px 14px", borderRadius:8,
                  border:`1.5px solid ${SW.amber}`, background:SW.amberSoft,
                  display:"flex", alignItems:"center", gap:12 }}>
      <span style={{ fontSize:15, lineHeight:1 }} aria-hidden="true">⚠</span>
      <div style={{ flex:1, fontSize:12.5, lineHeight:1.5, color:SW.ink }}>
        This design was restored from a file with incomplete plan geometry, so it may be out of date.
        Rebuild it from the saved plan to restore every line.
      </div>
      <button onClick={onRebuild} style={{ ...swBtn(true), whiteSpace:"nowrap" }}>↻ Rebuild from plan</button>
    </div>
  ) : null;

  if (!lines.length) return (
    <div>
      {staleBanner}
      <div style={{ marginTop:30, padding:36, border:`1px dashed ${SW.rule}`, borderRadius:10, textAlign:"center", color:SW.faint, fontSize:13, lineHeight:1.7 }}>
        No shear-wall lines yet.<br/>
        In the <b style={{color:SW.ink}}>Plan Sketcher</b>, drag wind sections across the plan, mark the walls that take point loads,
        then press <b style={{color:SW.accent}}>Design shear walls →</b>. Each point-load wall arrives here as a line carrying its
        reaction (kips) and wall height — parapets are not part of the shear-wall calc.
      </div>
      <div style={{ marginTop:14, display:"flex", alignItems:"center", gap:10 }}>
        <SwField label="Sheathing">
          <select value={g.grade === "str1" ? "str1" : "rated"} onChange={(e)=>setGl("grade",e.target.value)} style={selStyle}>
            <option value="rated">1/2&Prime; rated</option>
            <option value="str1">1/2&Prime; Structural I</option>
          </select>
        </SwField>
      </div>
      <SwScheduleRef grade={g.grade}/>
    </div>
  );

  return (
    <div onClick={()=>ctx&&setCtx(null)}>
      {/* Pinned constraints — sticks below the suite tab bar exactly like the sketcher ribbon (rev 5 --tabbar-h) */}
      <div style={{ position:"sticky", top:"var(--tabbar-h,42px)", zIndex:30, background:SW.sheet,
                    paddingTop:4, paddingBottom:6, boxShadow:`0 6px 8px -8px rgba(28,39,51,.25)` }}>
        <div style={{ display:"flex", alignItems:"center", gap:10, margin:"0 0 6px" }}>
          <span style={{ width:6, height:6, background:SW.accent, display:"inline-block", flex:"none" }} aria-hidden="true"/>
          <div style={{ fontSize:11, fontWeight:700, letterSpacing:"0.14em", textTransform:"uppercase", color:SW.accent }}>Design constraints</div>
          <div style={{ flex:1, height:1, background:SW.rule }} />
          {/* Floor switcher — flips which floor's design is shown (synced with the plan selector). Greyed until 2-story. */}
          <div title={twoStory ? "Switch which floor's design you're viewing" : "Two-story mode only"}
               style={{ display:"flex", alignItems:"center", gap:7, flex:"none", opacity: twoStory ? 1 : 0.45 }}>
            <span style={{ fontSize:10.5, fontWeight:700, letterSpacing:"0.12em", textTransform:"uppercase", color:SW.faint }}>Designing</span>
            <div style={{ display:"flex", border:`1.5px solid ${twoStory ? SW.accent : SW.rule}`, borderRadius:5, overflow:"hidden" }}>
              {[1,2].map(f=>(
                <button key={f} disabled={!twoStory} onClick={()=>twoStory&&setActiveFloor(f)}
                  style={{ border:0, padding:"4px 12px", fontFamily:MONO, fontSize:11, fontWeight:700, letterSpacing:"0.02em",
                           cursor: twoStory ? "pointer" : "default",
                           borderLeft: f===2 ? `1px solid ${SW.rule}` : "none",
                           background: (twoStory && activeFloor===f) ? SW.accent : "transparent",
                           color: (twoStory && activeFloor===f) ? "#fff" : SW.faint }}>
                  {f===1 ? "1st Floor" : "2nd Floor"}
                </button>
              ))}
            </div>
          </div>
        </div>
        <div style={{ display:"flex", flexWrap:"wrap", gap:8, alignItems:"flex-start" }}>
          <div style={{ flex:"1.4 1 280px", minWidth:240 }}>
            <PinCard title="Seismic" cols={2}>
              <PinRow label="Cs"><span style={{fontSize:12,fontWeight:600}}>{g.Cs ?? 0}</span></PinRow>
              <PinRow label="V = Cs·W" unit="lbs"><span style={{fontSize:12,fontWeight:700,color:SW.accent}}>{wTotal!=null ? Math.round((Number(g.Cs)||0)*wTotal).toLocaleString() : "—"}</span></PinRow>
              <PinRow label="S_DS"><input type="number" step={0.05} min={0} value={g.sds ?? 0} onChange={(e)=>setGl("sds",parseFloat(e.target.value)||0)} style={pinNumS}/></PinRow>
              <PinRow label="R" unit="ref"><span style={{fontSize:12,fontWeight:600,color:SW.faint}}>{g.R}</span></PinRow>
              {/* (rev 59) Cs is an INPUT on the Plan tab (side panel → Dead Loads); shown read-only here with
                  the design base shear V = Cs·W_total (W_total lifted from the Plan tab as `wTotal`, "—" in 2-Story).
                  (rev 61) g.vSeismic / g.R are now the post-R reduced convention — R is reference-only.
                  (rev 62) S_DS is editable here (drives E_v on uplift/compression, B=0.6−0.14·S_DS); seismic is now
                  applied PER LINE — each line carries its own seismic reaction from the plan, enveloped against wind
                  by the engine. The per-line seismic shear + governing case show in the selected-line results below. */}
            </PinCard>
          </div>
          <div style={{ flex:"1.4 1 280px", minWidth:240 }}>
            <PinCard title="Dimensions" cols={2}>
              <PinRow label="Min segment" unit="ft"><input type="number" step={0.5} value={d.minSegLen} onChange={(e)=>setDk("minSegLen",parseFloat(e.target.value)||0)} style={pinNumS}/></PinRow>
              <PinRow label="Max segment" unit="ft"><input type="number" step={0.5} value={d.maxSegLen} onChange={(e)=>setDk("maxSegLen",parseFloat(e.target.value)||0)} style={pinNumS}/></PinRow>
              <PinRow label="Max segs"><select value={d.maxSegments} onChange={(e)=>setDk("maxSegments",+e.target.value)} style={pinSelS}>{[1,2,3,4,5,6].map(n=><option key={n} value={n}>{n}</option>)}</select></PinRow>
              <PinRow label="Snap" unit="ft"><select value={d.snap} onChange={(e)=>setDk("snap",+e.target.value)} style={pinSelS}><option value={0.25}>0.25</option><option value={0.5}>0.5</option><option value={1}>1.0</option></select></PinRow>
              <PinRow label="Thickness" unit="in"><select value={d.thickness} onChange={(e)=>setDk("thickness",+e.target.value)} style={pinSelS}><option value={3.5}>3.5</option><option value={5.5}>5.5</option><option value={7.25}>7.25</option></select></PinRow>
              <PinRow label="HD dist" unit="in"><input type="number" step={0.5} value={d.hdDist} onChange={(e)=>setDk("hdDist",parseFloat(e.target.value)||0)} style={pinNumS}/></PinRow>
            </PinCard>
          </div>
          <div style={{ flex:"1 1 210px", minWidth:200 }}>
            <PinCard title="Plywood" cols={1}>
              <PinRow label="Sheathing" grow><select value={g.grade === "str1" ? "str1" : "rated"} onChange={(e)=>setGl("grade",e.target.value)} style={{ ...pinSelS, width:"100%", flex:"1 1 auto", minWidth:0 }}><option value="rated">1/2&Prime; rated</option><option value="str1">1/2&Prime; Structural I</option></select></PinRow>
              <PinRow label="Max SW type" grow><select value={d.maxType} onChange={(e)=>setDk("maxType",+e.target.value)} style={{ ...pinSelS, width:"100%", flex:"1 1 auto", minWidth:0 }}><option value={1}>1</option><option value={2}>2</option><option value={3}>3</option></select></PinRow>
              <div style={{ gridColumn:"1 / -1", marginTop:1, fontSize:10.5, color:SW.faint, lineHeight:1.55 }}>
                <div style={{ display:"flex", justifyContent:"space-between" }}><span>Allow. W (plf)</span><span style={{ fontFamily:MONO, color:SW.ink, fontWeight:600 }}>{schedFor(g.grade).slice(0,3).map((t)=>t.wind).join("/")}</span></div>
                <div style={{ display:"flex", justifyContent:"space-between" }}><span>Allow. S (plf)</span><span style={{ fontFamily:MONO, color:SW.ink, fontWeight:600 }}>{schedFor(g.grade).slice(0,3).map((t)=>t.seismic).join("/")}</span></div>
              </div>
            </PinCard>
          </div>
          <div style={{ flex:"1 1 230px", minWidth:210 }}>
            <PinCard title="Other constraints" cols={1}>
              <PinRow label="Objective" grow><select value={d.objective} onChange={(e)=>setDk("objective",e.target.value)} style={{ ...pinSelS, width:"100%", flex:"1 1 auto", minWidth:0 }}><option value="length">Min. wall length</option><option value="nailing">Min. nailing (type)</option></select></PinRow>
              <PinRow label="Anchored into" grow><select value={d.anchor} onChange={(e)=>setDk("anchor",e.target.value)} style={{ ...pinSelS, width:"100%", flex:"1 1 auto", minWidth:0 }}><option>Concrete</option><option>Masonry</option><option>Wood</option></select></PinRow>
              <button style={{ ...swBtn(true), gridColumn:"1 / -1", marginTop:2, padding:"0 12px", height:PIN_H, boxSizing:"border-box", fontSize:11, ...(optimizeStaleHint ? STALE_BTN : {}) }}
                title={optimizeStaleHint ? "Design inputs changed since you last optimized — re-optimize to update the design" : undefined}
                onClick={optimizeAll}>{optimizeStaleHint && WARN}⚡ Optimize design</button>
            </PinCard>
          </div>
        </div>
      </div>
      <div style={{ fontSize:11, color:SW.faint, marginTop:6 }}>
        Line force and wall height come from the Plan Sketcher: W<sub>WIND</sub> per line = its wind reaction, and (rev 62) each line also carries its own <b>seismic</b> reaction (V = C<sub>s</sub>·W_total distributed on the plan) — the engine designs each line for the heavier of the two, per element. C<sub>s</sub> is set on the Plan tab; S<sub>DS</sub> (E_v) is editable here; code &amp; species come from the Calculation sheet; dead loads and sheathing grade are shared. Demand shear = line force ÷ total wall length on that line.
      </div>

      {genMsg && (
        <div style={{ marginTop:12, padding:"8px 12px", fontSize:12, fontFamily:MONO, borderRadius:6,
                      background:genMsg.ok?SW.greenSoft:SW.redSoft, color:genMsg.ok?SW.green:SW.red,
                      border:`1px solid ${genMsg.ok?SW.green:SW.red}` }}>
          {genMsg.text}
        </div>
      )}

      <SectionTitle
        right={
          <div style={{ display:"flex", gap:8, alignItems:"center" }}>
            <button onClick={()=>setShowTags(v=>!v)} style={{ ...swBtn(showTags), padding:"4px 12px", fontSize:11 }}
                    title="Show or hide the SW-A / SW-B wall marks on the plan">
              {showTags ? "Hide wall tags" : "Show wall tags"}
            </button>
            <div style={{ padding:"4px 10px", border:`1.5px solid ${allPass?SW.green:SW.red}`, borderRadius:6,
                          background:allPass?SW.greenSoft:SW.redSoft, color:allPass?SW.green:SW.red,
                          fontFamily:MONO, fontSize:11, fontWeight:700 }}>
              {allPass ? "✓ ALL LINES PASS" : "✕ NOT PASSING"}
            </div>
          </div>
        }>
        Plan — live recalculation
      </SectionTitle>

      <DesignPlan shape={shape} lines={lines} marks={wallMarks} showTags={showTags} lineNames={lineNames}
                  segsByLine={segsByLine} setSegsByLine={setSegsByLine}
                  resultsByLine={resultsByLine} selLine={selLine} setSelLine={setSelLine}
                  snap={d.snap} maxSegLen={d.maxSegLen}
                  onCtx={(e, lineId, idx)=>{ setSelLine(lineId); setCtx({ px:Math.min(e.clientX, window.innerWidth-280), py:Math.min(e.clientY, window.innerHeight-240), lineId, idx }); }}/>

      {/* per-line chips */}
      <div style={{ display:"flex", flexWrap:"wrap", gap:8, marginTop:10 }}>
        {lines.map(ln=>{
          const rs=resultsByLine[ln.id]||[]; const pass=rs.length>0&&rs.every(r=>!r.failed);
          const isSel=selLine===ln.id;
          return (
            <button key={ln.id} onClick={()=>setSelLine(ln.id)}
              style={{ padding:"6px 12px", fontFamily:MONO, fontSize:12, cursor:"pointer", borderRadius:6,
                       border:`1.5px solid ${isSel?SW.accent:SW.rule}`,
                       background:isSel?SW.accentSoft:SW.panel,
                       color: rs.length? (pass?SW.green:SW.red) : SW.faint }}>
              {lineNames[ln.id]} · {fmt(ln.forceLbs/1000,2)}k · {fmt(ln.lengthFt,0)}′ {rs.length? (pass?"✓":"✕") : "·"}
            </button>
          );
        })}
      </div>

      {sel && (
        <>
          <SectionTitle
            right={
              <div style={{ display:"flex", gap:8 }}>
                <button style={swBtn(false)} onClick={()=>addSeg(sel.id)} disabled={selSegs.length>=6}>+ Add wall</button>
                <button style={calcStaleHint ? {...swBtn(false), ...STALE_BTN} : swBtn(false)}
                  title={calcStaleHint ? "This line changed since you last sent it — click to update the Calculation Sheet" : undefined}
                  onClick={()=>applyToCalc(sel, selSegs, selRes, d, lineLabel(sel), selSegs.map((_,i)=>wallMarks[sel.id+"|"+i]))}>{calcStaleHint && WARN}Send line to calculation sheet →</button>
              </div>
            }>
            Selected line — {lineNames[sel.id]} · {sel.windAxis==="h"?"E–W":"N–S"} · wind {fmt(sel.forceLbs/1000,2)}k · seismic {fmt((sel.forceLbsSeismic||0)/1000,2)}k · {fmt(sel.lengthFt,1)} ft · H {fmt(sel.heightFt,1)} ft
          </SectionTitle>
          {selSegs.length === 0 ? (
            <div style={{ padding:20, border:`1px dashed ${SW.rule}`, borderRadius:8, color:SW.faint, fontSize:12 }}>
              No shear walls on this line yet — press ⚡ Optimize design, or + Add wall.
            </div>
          ) : (
          <>
          {stacking && (
            <div style={{ margin:"2px 0 10px", padding:"8px 12px", borderRadius:7,
                          border:`1px solid ${SW.accent}`, background:SW.accentSoft||"rgba(35,87,127,0.06)",
                          fontSize:11, lineHeight:1.5, color:SW.ink }}>
              <b style={{ color:SW.accent }}>2-story stacking active.</b> Every row below is re-derived from the
              <b> arm-aware</b> overturning of both stories — the roof reaction acts a full upper story higher
              (arm H₁+H₂), so its moment adds on top of the 2nd-floor moment
              (M<sub>base</sub> = M<sub>1st</sub> + M<sub>2nd</sub>), not a flat sum of the reactions. End post,
              uplift, holdown, anchor, strap, deflection and footing all reflect the stacked demand, now for
              <b> both wind and seismic</b> (each line carries its per-floor seismic force). The
              <b> upper-story dead load</b> stacks too (rev 63): it resists uplift (smaller holdowns) while adding
              to the end-post compression, through each case's factored bucket; the footing base shear is cumulative.
              Wind/seismic shear and nailing are unchanged (the combined story shear was already carried). Δ uses the
              stacked (stiffer) end post, so the 1st-floor inter-story drift can read smaller than the single-story value.
            </div>
          )}
          <div className="sw-scroll">
            <table className="sw-table" style={{ minWidth:700, color:SW.ink }}>
              <thead>
                <tr style={{ borderBottom:`1.5px solid ${SW.faint}` }}>
                  <th style={{ textAlign:"left", padding:"4px 10px", fontSize:11 }}></th>
                  {selSegs.map((_, i) => (
                    <th key={i} style={{ padding:"4px 8px", fontSize:11, fontFamily:MONO, color:SW.accent }}>SW-{wallMarks[selLine+"|"+i] || (i+1)}</th>
                  ))}
                </tr>
              </thead>
              <tbody>
                <Row label="Length / position" unit="ft" cells={selRes} render={(r, i) => (
                  <span style={{ fontFamily:MONO, fontSize:12 }}>{fmt(selSegs[i].length,2)} <span style={{ color:SW.faint, fontSize:10 }}>@ {fmt(selSegs[i].start,2)}</span></span>
                )} />
                <Row label="Wall height h" unit="ft" cells={selRes} render={() => (
                  <span style={{ fontFamily:MONO, fontSize:12 }}>{fmt(sel.heightFt,2)}</span>
                )} />
                <Row label="Aspect ratio h/L" cells={selRes} render={(r) => <Chip v={r.aspectNG ? "NG!" : r.aspect} d={2} />} />
                <Row label="Wind shear v" unit="plf" cells={selRes} render={(r) => <Chip v={r.vW} d={1} />} />
                <Row label="Seismic shear v" unit="plf" cells={selRes} render={(r) => <Chip v={r.vS} d={2} />} />
                <Row label="Shear wall nailing" cells={selRes} render={(r) => {
                  if (!isNum(r.selType)) return <Chip v={r.autoType} />;
                  const bad = r.ovBad && r.ovBad.type;
                  return (
                    <span style={{ fontFamily:MONO, fontSize:12, color: bad ? SW.red : SW.ink }}>
                      {NAIL_EDGE[r.selType]}<CaseTag which={_govShearCase(r, g.grade)} />
                      <div style={{ fontSize:10, color: bad ? SW.red : SW.faint }}>
                        Type {r.selType}{bad ? ` — requires Type ${r.autoType}` : ""}
                      </div>
                    </span>
                  );
                }} />
                <Row label="Allowable wind / seismic" unit="plf" cells={selRes} render={(r) => {
                  const t = isNum(r.selType) ? schedFor(g.grade)[r.selType-1] : null;
                  return t ? <span style={{ fontFamily:MONO, fontSize:12 }}>{t.wind} / {fmt(r.factor*t.seismic,0)}</span> : <Chip v="—" />;
                }} />
                {stacking && (
                  <Row label="Overturning M · stacked" unit="k·ft" cells={selRes} render={(r) => {
                    const m = xMax(r.MotW, r.MotS);
                    return <span style={{ fontFamily:MONO, fontSize:12, color:SW.accent, fontWeight:700 }}>{fmt(m/1000,1)}</span>;
                  }} />
                )}
                <Row label="End post" cells={selRes} render={(r) => <span><Chip v={r.ovBad&&r.ovBad.post?"NG!":r.dispPost} /><CaseTag which={_govBy(r.compS, r.compW)} /></span>} />
                <Row label="Max uplift" unit="lbs" cells={selRes} render={(r) => <Chip v={r.maxUplift === 0 ? "—" : r.maxUplift} d={0} />} />
                <Row label="Holdown" cells={selRes} render={(r) => <span><Chip v={r.ovBad&&r.ovBad.hd?"NG!":r.dispHd} />{r.maxUplift>0 && <CaseTag which={_govBy(r.upHD_S, r.upHD_W)} />}</span>} />
                <Row label="Anchor" cells={selRes} render={(r) => <Chip v={r.anchorSel} />} />
                <Row label="Strap alternative" cells={selRes} render={(r) => <Chip v={r.altStrap} />} />
                <Row label="Δ wind" unit="in" cells={selRes} render={(r) => <Chip v={isFinite(r.deflW) ? r.deflW : "—"} d={3} />} />
                <Row label="Req. footing length" unit="ft" cells={selRes} render={(r) => <span><Chip v={isFinite(r.reqFtgLen) ? r.reqFtgLen : "—"} d={2} />{isFinite(r.reqFtgLen) && <CaseTag which={_govBy(r.LminS, r.LminW)} />}</span>} />                <Row label="Status" cells={selRes} render={(r) => <Chip v={r.failed ? "FAILED!!!" : "OK"} />} />
              </tbody>
            </table>
          </div>
          </>
          )}
        </>
      )}

      <SwScheduleRef grade={g.grade}/>

      <SwCtxMenu ctx={ctx} lines={lines} segsByLine={segsByLine} resultsByLine={resultsByLine}
                 setOv={setOv} onRemove={removeSeg} onClose={()=>setCtx(null)} thickness={d.thickness}/>
    </div>
  );
}

/* ════════════════════════════════════════════════════════════════════════
   APP SHELL — Plan Sketcher · Calculation Sheet · Design
   The sketcher stays mounted (hidden) so the plan survives tab switches.
   ════════════════════════════════════════════════════════════════════════ */
// ── App-level design system (rev 9): Plex type, grid-paper signature, focus rings, micro-interactions ──
const APP_CSS = `
@import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500;600;700&family=IBM+Plex+Sans:wght@400;500;600;700;800&display=swap');

/* Engineer's quad-ruled paper: faint 22px grid, heavier rule every 5th line (110px) */
.paper-desk{
  background-color:#EFEDE6;
  background-image:
    linear-gradient(rgba(35,87,127,.12) 1px, transparent 1px),
    linear-gradient(90deg, rgba(35,87,127,.12) 1px, transparent 1px),
    linear-gradient(rgba(35,87,127,.06) 1px, transparent 1px),
    linear-gradient(90deg, rgba(35,87,127,.06) 1px, transparent 1px);
  background-size:110px 110px, 110px 110px, 22px 22px, 22px 22px;
}
/* Suite tab bar as a drawing title block */
.tbar{ box-shadow:0 1px 0 rgba(28,39,51,.06); }
/* (rev 69) persistent file toolbar — sits above the tab bar inside the sticky header; reachable on every tab */
.apphdr{ box-shadow:0 2px 10px -7px rgba(28,39,51,.35); }
.filebar{ display:flex; align-items:center; gap:6px; padding:5px 16px; background:#ECEAE2; border-bottom:1px solid #D8D4C8; }
.filebar .fblabel{ font-family:'IBM Plex Mono',ui-monospace,monospace; font-size:10.5px; letter-spacing:.22em;
  color:#586470; font-weight:600; text-transform:uppercase; margin-right:8px; }
.filebtn{ border:1px solid #D8D4C8; background:#FFFFFF; color:#1C2733; font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;
  font-size:11.5px; font-weight:600; padding:4px 12px; border-radius:4px; cursor:pointer;
  transition:border-color .14s ease, color .14s ease, background .14s ease; }
.filebtn:hover{ border-color:#23577F; color:#23577F; background:#F6F9FB; }
.filebtn:active{ box-shadow:inset 0 1px 3px rgba(28,39,51,.18); }
/* (rev 70) project-name input, group separator, and last-saved status in the file bar */
.fbname{ border:1px solid #D8D4C8; background:#FFFFFF; color:#1C2733; font-family:'IBM Plex Sans','Helvetica Neue',Arial,sans-serif;
  font-size:11.5px; font-weight:600; padding:4px 9px; border-radius:4px; width:170px; margin-right:4px;
  transition:border-color .14s ease, box-shadow .14s ease; }
.fbname:focus{ outline:none; border-color:#23577F; box-shadow:0 0 0 2px rgba(35,87,127,.15); }
.fbname::placeholder{ color:#6B7480; font-weight:500; }
.fbsep{ width:1px; align-self:stretch; margin:2px 6px; background:#D8D4C8; }
.fbstatus{ margin-left:auto; font-family:'IBM Plex Mono',ui-monospace,monospace; font-size:10.5px; font-weight:600;
  letter-spacing:.04em; color:#586470; white-space:nowrap; }
@media print{ .filebar{ display:none; } }
.tbrand{ border-right:1px solid #DAD6CA; align-self:stretch; display:flex; flex-direction:column; justify-content:center; }
.tbrand small{ font-family:'IBM Plex Mono',ui-monospace,monospace; font-size:10.5px; letter-spacing:.22em; color:#586470; font-weight:500; }
.ttab{ position:relative; transition:color .14s ease, background .14s ease; }
.ttab:hover{ color:#23577F !important; background:#F1F5F8 !important; }
.ttab .teye{ font-family:'IBM Plex Mono',ui-monospace,monospace; font-size:10.5px; letter-spacing:.18em; font-weight:500;
  color:inherit; opacity:.65; display:block; text-align:left; margin-bottom:1px; }
/* Quality floor: visible keyboard focus, calm motion, honest print */
button:focus-visible, select:focus-visible, input:focus-visible{ outline:2px solid #23577F; outline-offset:1.5px; border-radius:4px; }
.sw-root button, .lt-root button{ transition:filter .14s ease, border-color .14s ease, box-shadow .14s ease; }
.sw-root button:hover, .lt-root button:hover{ filter:brightness(.965); }
.sw-root select, .sw-root input[type=number], .lt-root select, .lt-root input[type=number]{ transition:border-color .14s ease, box-shadow .14s ease; }
.sw-root select:hover, .sw-root input[type=number]:hover, .lt-root select:hover, .lt-root input[type=number]:hover{ border-color:#23577F !important; }
.sw-root input[type=number]:focus, .lt-root input[type=number]:focus{ border-color:#23577F !important; box-shadow:0 0 0 2.5px #E8EFF4; }
.sw-root, .lt-root{ font-variant-numeric:tabular-nums; }
@media (prefers-reduced-motion: reduce){ .ttab, .sw-root button, .lt-root button{ transition:none; } }
@media print{ .paper-desk{ background-image:none !important; background-color:#FFF !important; } }
`;

// ── PROJECT-FILE DEFAULTS + VERSIONING ──────────────────────────────────────
// These are the single source of truth for the shapes the loader REPLACES wholesale
// (calc.g, design.d, calc.segments). Both the useState inits below and loadProject() below
// consume them, so any field ADDED here in the future auto-fills its default on an OLD file
// (the dominant forward-compat risk: a wholesale setG/setD/setSegments leaving a new field
// `undefined`). Keep these byte-faithful to the prior inline inits — a value change here is a
// behavior change for current files. NOTE: `g.grade` defaults to "str1" (Structural I) — rev 65, by
// request. It now rides in DEFAULT_G, so new sessions default to Structural I AND a toggled grade
// round-trips through save/load via the {...DEFAULT_G, ...calc.g} merge. An OLD file with no stored
// grade reopens as "str1" (no live .wps files predate this; the engine still reads a falsy grade as
// "rated"). To revert the default, set grade:"rated" here.
const DEFAULT_G   = { code:4, species:1, line:"1", vSeismic:5, sds:1, R:6.5, wWind:26000, roofDL:20, floorDL:0, wallDL:15, Cs:0.05, grade:"str1" };
const DEFAULT_D   = { thickness:5.5, anchor:"Concrete", roofTrib:2, floorTrib:0, hdDist:5,
                      minSegLen:4, maxSegLen:12, maxSegments:4, maxType:3, snap:0.5,
                      objective:"length", ftgWidth:1.33, ftgThick:12, height:15, lineLength:40 };
const SEG_DEFAULTS= { length:0, height:15, roofTrib:10, floorTrib:0, hdDist:5, thickness:5.5, anchor:"Concrete", selType:1, ftgWidth:1.33, ftgThick:12 };
// Design-tab collections (rev 24). A design LINE is { id, key, windAxis, o, a, b, lengthFt, heightFt,
// forceLbs }. Only the SCALAR fields are defaultable — the GEOMETRY (id/key/windAxis/o/a/b) cannot be
// invented, so it is NOT in DEFAULT_LINE; a line missing geometry is filtered + flagged stale in
// loadProject (it's regenerable from the saved plan). A PLACED shear-wall segment is { start, length,
// ov? } — ov rides along in the spread and is already (s.ov||{})-tolerant downstream.
const DEFAULT_LINE   = { lengthFt:0, heightFt:13, forceLbs:0, forceLbsSeismic:0 };
const DEFAULT_PLACED = { start:0, length:0 };

// Save-file schema version. WRITTEN by onSave and now READ by the loader (it used to be
// decorative). Bump this on every schema change and add the matching MIGRATIONS step.
const CURRENT_VERSION = 3;
// Step migrations: MIGRATIONS[k] takes a project AT version k and returns it AT version k+1.
// 1→2 is purely ADDITIVE — v2 only adds optional ui/camera/selection fields the loader already
// feature-detects — so there is no data transform, we only stamp the version. This ladder exists
// so the NEXT (possibly breaking) change has a home. Merge-on-defaults below handles ADDED fields
// automatically; RENAMES and UNIT/SEMANTICS changes do NOT — they need an explicit step here, e.g.:
//
//   2: (p) => ({                                 // hypothetical v2 → v3
//     ...p,
//     design: { ...p.design, lines: (p.design?.lines||[]).map(l => ({
//       ...l,
//       forceN:  l.forceLbs * 4.4482216,         // UNIT change: lbs → newtons (same datum, new meaning)
//       // forceLbs intentionally dropped after the rename
//     })) },
//     version: 3,
//   }),
//
// Whenever you add a step: bump CURRENT_VERSION, FREEZE a fixture at the OLD version, and add a
// test asserting that old fixture loads to the NEW correct value (the only thing that catches a
// botched unit conversion — see the migration checklist in the handoff §4x / §7).
const MIGRATIONS = {
  1: (p) => ({ ...p, version:2 }),
  // 2→3 (rev 61): UNIT/SEMANTICS change. The engine dropped the /R from E_seis, so g.vSeismic
  // now means the post-R (ASCE 7 reduced) seismic base shear in lbs — it used to be stored as
  // "lbs·R" (un-reduced). Convert by dividing the OLD value by the stored R (DEFAULT_G.R when the
  // file predates an R field). g.R itself is preserved (now reference-only). This runs BEFORE
  // merge-onto-defaults, so guard for a missing calc/g.
  2: (p) => {
    const g = p && p.calc && p.calc.g;
    if (g && Number.isFinite(g.vSeismic)) {
      const R = Number.isFinite(g.R) && g.R !== 0 ? g.R : DEFAULT_G.R;
      return { ...p, calc: { ...p.calc, g: { ...g, vSeismic: g.vSeismic / R } }, version:3 };
    }
    return { ...p, version:3 };
  },
};
// Walk a loaded project up to `target` one step at a time. `migrations`/`target` are injectable so a
// test can prove the MECHANISM (ordering + value transforms) with a synthetic ladder even while the
// real MIGRATIONS[1] is a no-op stamp. Returns the migrated project + `newer` (file from a future build).
function migrateProject(raw, migrations = MIGRATIONS, target = CURRENT_VERSION){
  const p = raw || {};
  let v = (typeof p.version === "number") ? p.version : 1;   // pre-version / junk → treat as v1
  const newer = v > target;
  let out = p;
  while(v < target && migrations[v]){ out = migrations[v](out); v = out.version; }
  return { project: out, newer };
}
// Pure load normalizer: migrate, then merge every wholesale-replaced object onto its DEFAULT_*
// so missing fields fill in. PRESERVES the loader's exact present-checks (g/segments/d are only
// applied when present in the file; tab/hlSel/selLine keep their prior fallbacks) so current v1
// AND v2 files resolve to byte-identical state. Returns ready-to-dispatch slices + the migrated
// project (for the same `if(project.design)`/`if(project.calc)` guards the handler always used).
function loadProject(raw){
  const { project, newer } = migrateProject(raw);
  const calc   = project.calc   || {};
  const design = project.design || {};
  const ui     = project.ui     || {};
  // design lines: merge scalar/future fields onto DEFAULT_LINE, but NEVER invent geometry. A line
  // missing a/b can't be rendered or designed, so it is EXCLUDED and the design is flagged STALE —
  // the saved plan is intact, so a rebuild regenerates every line (the "flag + prompt re-run" choice,
  // not a silent drop). placed segments merge onto DEFAULT_PLACED; ALL segsByLine keys are kept (even
  // for a filtered line) so a rebuild can restore that line's layout by id.
  // Back-compat: old files stored a single `design.lines` array (1-story); newer files store
  // `design.linesByFloor` ({1:[...],2:[...]}). Normalize either into linesByFloor.
  const hasGeom  = (l) => !!(l && l.id != null && Number.isFinite(l.lengthFt) && l.lengthFt > 0 &&
                             l.a && Number.isFinite(l.a.x) && Number.isFinite(l.a.y) &&
                             l.b && Number.isFinite(l.b.x) && Number.isFinite(l.b.y));
  const rawByFloor = (design.linesByFloor && typeof design.linesByFloor === "object")
    ? design.linesByFloor
    : { 1: (Array.isArray(design.lines) ? design.lines : []) };   // legacy single-array → floor 1
  const linesByFloor = {};
  let stale = false;
  for(const fk in rawByFloor){
    const merged = (Array.isArray(rawByFloor[fk]) ? rawByFloor[fk] : []).map(l => ({ ...DEFAULT_LINE, ...l }));
    const valid  = merged.filter(hasGeom);
    if(valid.length < merged.length) stale = true;                 // some saved line lacked geometry
    linesByFloor[fk] = valid;
  }
  if(!linesByFloor[1]) linesByFloor[1] = [];                       // always have a floor-1 slot
  const sblIn    = design.segsByLine || {};
  const segsByLine = {};
  for(const k in sblIn) segsByLine[k] = (Array.isArray(sblIn[k]) ? sblIn[k] : []).map(s => ({ ...DEFAULT_PLACED, ...s }));
  // calc sub-tabs (rev 132): prefer the tab model; fall back to a legacy single `calc.segments` wrapped
  // into one tab; else null (handler keeps the running state). Each tab's segments are merged onto
  // SEG_DEFAULTS and padded to 6 columns (the sheet's fixed width). wWind defaults to the saved g.wWind.
  const seg6 = (arr) => Array.from({ length:6 }, (_, i) => ({ ...SEG_DEFAULTS, ...((Array.isArray(arr) ? arr : [])[i] || {}) }));
  const gW = (calc.g && Number.isFinite(calc.g.wWind)) ? calc.g.wWind : DEFAULT_G.wWind;
  let calcTabs = null, activeCalcId = null;
  if (Array.isArray(calc.tabs) && calc.tabs.length) {
    calcTabs = calc.tabs.map((t, i) => ({
      id:      (t && t.id) || ("calc-" + (i + 1)),
      name:    (t && typeof t.name === "string" && t.name) || ("Wall " + (i + 1)),
      lineId:  (t && t.lineId != null) ? t.lineId : null,
      marks:   (t && Array.isArray(t.marks)) ? t.marks : null,
      segments: seg6(t && t.segments),
      wWind:   (t && Number.isFinite(t.wWind)) ? t.wWind : gW,
    }));
    activeCalcId = calcTabs.find((t) => t.id === calc.activeCalcId) ? calc.activeCalcId : calcTabs[0].id;
  } else if (Array.isArray(calc.segments)) {
    calcTabs = [{ id:"calc-1", name:"Wall 1", lineId:null, marks:null, segments: seg6(calc.segments), wWind: gW }];
    activeCalcId = "calc-1";
  }
  return {
    newer, project,
    calc: {
      g:        calc.g        ? { ...DEFAULT_G, ...calc.g }                    : undefined,
      segments: calc.segments ? calc.segments.map(s => ({ ...SEG_DEFAULTS, ...s })) : undefined,
      tabs: calcTabs, activeCalcId,
    },
    design: {
      linesByFloor, stale, segsByLine,
      shape:      design.shape || null,
      d:          design.d ? { ...DEFAULT_D, ...design.d } : undefined,
      selLine:    design.selLine !== undefined ? design.selLine : null,
    },
    ui: { tab: ui.tab || "plan", hlSel: ("hlSel" in ui) ? ui.hlSel : null,
          twoStory: ("twoStory" in ui) ? !!ui.twoStory : false,   // old files lack it → single story
          activeFloor: ui.activeFloor === 2 ? 2 : 1 },
  };
}

export default function App() {
  const [tab, setTab] = useState("plan");
  const [g, setG] = useState(DEFAULT_G);
  const [wTotal, setWtotal] = useState(null);   // (rev 58) 1-story seismic W_total lifted from PlanSketcher; null in 2-Story (pending)
  const setGl = (key, val) => setG((p) => ({ ...p, [key]: val }));

  const mkSeg = (length, roofTrib) => ({ ...SEG_DEFAULTS, length, roofTrib });
  // ── CALCULATION-SHEET SUB-TABS (rev 132) ──
  // The Calculation Sheet is now a Chrome-style tabbed surface: each sub-tab is one shear-wall LINE
  // (its own 6-segment layout + its own wind force `wWind`). A tab carries:
  //   { id, name, lineId, marks, segments, wWind }
  // `lineId` ties an auto sub-tab to the Design line it came from (re-pushing that line UPDATES the
  // same tab instead of duplicating). `lineId:null` = a MANUAL tab added with the "+" button, run
  // independently of the Design tab's Optimize. `marks` mirrors the Design tab's wall marks so the
  // per-segment "SW-A / SW-B" labels match across tabs. Building-wide config (code/species/grade/
  // seismic/dead loads) stays in the shared `g`; only `wWind` is per-tab (each wall a different force).
  const mkCalcSegs = () => [ mkSeg(5,2), mkSeg(5,2), mkSeg(0,10), mkSeg(0,10), mkSeg(0,10), mkSeg(0,10) ];
  const calcSeq = useRef(2);                                  // next manual id counter ("calc-2", …)
  const newCalcId = () => "calc-" + (calcSeq.current++);
  const [calcTabs, setCalcTabs] = useState(() => [
    { id:"calc-1", name:"Wall-1 (default)", lineId:null, marks:null, segments:mkCalcSegs(), wWind:DEFAULT_G.wWind },
  ]);
  const [activeCalcId, setActiveCalcId] = useState("calc-1");
  const activeCalc = calcTabs.find((t) => t.id === activeCalcId) || calcTabs[0] || null;
  const segments = activeCalc ? activeCalc.segments : mkCalcSegs();
  const calcMarks = activeCalc ? activeCalc.marks : null;
  // effective globals for the ACTIVE tab = shared g with this tab's own wind force spliced in
  const gEff = useMemo(() => (activeCalc ? { ...g, wWind: activeCalc.wWind } : g), [g, activeCalc]);
  // CalcSheet edits a segment in the ACTIVE tab; supports both function- and value-style updates.
  const setSegments = (updater) => setCalcTabs((prev) => prev.map((t) => t.id === activeCalcId
    ? { ...t, segments: typeof updater === "function" ? updater(t.segments) : updater } : t));
  // CalcSheet's globals editor: `wWind` is per-tab, everything else is the shared building config.
  const setGlCalc = (key, val) => {
    if (key === "wWind") setCalcTabs((prev) => prev.map((t) => t.id === activeCalcId ? { ...t, wWind: val } : t));
    else setGl(key, val);
  };
  const totalL = segments.reduce((a, s) => a + s.length, 0);
  const results = useMemo(() => segments.map((s) => calcSegment(s, gEff, totalL)), [segments, gEff, totalL]);
  // light calc sheet consumes util-augmented results (engine untouched)
  const resultsU = useMemo(() => results.map((r, i) => withUtil(r, segments[i], g.grade)), [results, segments, g.grade]);
  const actU = resultsU.filter((r) => r.active);
  const calcOK = actU.length > 0 && actU.every((r) => r.pass);
  // Per-tab pass/fail for the sub-tab dots: run the (untouched) engine once per tab with that tab's
  // own wind force. Tabs are few, so this is cheap. "none" = no active wall on that tab yet.
  const calcTabStatus = useMemo(() => {
    const m = {};
    calcTabs.forEach((t) => {
      const tl = t.segments.reduce((a, s) => a + s.length, 0);
      const ge = { ...g, wWind: t.wWind };
      const rs = t.segments.map((s) => withUtil(calcSegment(s, ge, tl), s, g.grade)).filter((r) => r.active);
      m[t.id] = rs.length ? (rs.every((r) => r.pass) ? "ok" : "fail") : "none";
    });
    return m;
  }, [calcTabs, g]);
  const [hlSel, setHlSel] = useState(null); // column highlight (calc sheet)
  // Switch the visible sub-tab (clears the cross-table column highlight, which is per-tab).
  const selectCalcTab = (id) => { setActiveCalcId(id); setHlSel(null); };
  // "+" button — a fresh manual calc, independent of the Design tab's Optimize.
  const addCalcTab = () => {
    const id = newCalcId();
    const n = calcTabs.filter((t) => !t.lineId).length + 1;
    setCalcTabs((prev) => [...prev, { id, name:`Custom ${n}`, lineId:null, marks:null, segments:mkCalcSegs(), wWind:DEFAULT_G.wWind }]);
    selectCalcTab(id);
    setTab("calc");
  };
  // Close a sub-tab; if it was active, fall to a neighbour. The bar always keeps ≥1 tab.
  const closeCalcTab = (id) => setCalcTabs((prev) => {
    if (prev.length <= 1) return prev;                        // never empty the bar
    const idx = prev.findIndex((t) => t.id === id);
    const next = prev.filter((t) => t.id !== id);
    if (id === activeCalcId) selectCalcTab((next[idx] || next[idx - 1] || next[0]).id);
    return next;
  });
  // Inline rename of a MANUAL tab (auto tabs mirror their Design line and are renamed on re-send).
  // Double-click → the tab title becomes an editable input (no pop-up); Enter/blur commits, Esc cancels.
  const [editingCalcId, setEditingCalcId] = useState(null);
  const [editName, setEditName] = useState("");
  const startRenameCalc = (id) => {
    const t = calcTabs.find((x) => x.id === id); if (!t || t.lineId) return;   // manual tabs only
    setEditName(t.name); setEditingCalcId(id);
  };
  const commitRenameCalc = () => {
    const nm = editName.trim();
    if (editingCalcId != null && nm) setCalcTabs((prev) => prev.map((x) => x.id === editingCalcId ? { ...x, name:nm } : x));
    setEditingCalcId(null);
  };
  const cancelRenameCalc = () => setEditingCalcId(null);
  // ── TWO-STORY MODE (Step 1: UI scaffold only — no second plan, no calc change yet) ──
  const [twoStory, setTwoStory]     = useState(false);   // false = single story (today's behavior, untouched)
  const [activeFloor, setActiveFloor] = useState(1);     // sketcher view: 1 = 1st floor, 2 = 2nd floor

  // Design state (fed from the sketcher). Two-story keeps BOTH floors' designs keyed by floor;
  // `designLines` is the active floor's lines (derived), so the Design tab + everything downstream is unchanged.
  const [designLinesByFloor, setDesignLinesByFloor] = useState({});  // { 1:[...], 2:[...] }  (1-story → { 1:[...] })
  const designLines = useMemo(()=> designLinesByFloor[activeFloor] || designLinesByFloor[1] || designLinesByFloor[2] || [],
                              [designLinesByFloor, activeFloor]);
  const [designShape, setDesignShape] = useState(null);
  const [segsByLine, setSegsByLine] = useState({});
  const [d, setD] = useState(DEFAULT_D);
  const setDk = (k, v) => setD((p) => ({ ...p, [k]: v }));
  const [selLine, setSelLine] = useState(null);   // selected design line — lifted from DesignTab so save/load restores it
  const [designStale, setDesignStale] = useState(false);  // rev 24: a loaded file had geometry-less lines → prompt rebuild. Derived on load, NOT serialized (a re-save heals to the valid subset).
  // rev 130: what was last pushed to the Calculation Sheet — { lineId, sig }. Drives the red
  // "stale" look on the Design tab's "Send line to calculation sheet" button when the currently
  // selected line is the one in the sheet AND its pushable data has since changed. Live-session
  // only (NOT serialized): reset on New/Open so a loaded file is treated as in sync.
  const [calcPush, setCalcPush] = useState(null);
  // rev 130b: signature of the inputs the Design-tab ⚡ Optimize design optimizer last ran on. The
  // Optimize button (which produces the tab's design output) goes red when an input has changed since.
  // Lives in App (not DesignTab) so it survives the Design tab unmounting on a tab switch. Live-session
  // only; reset on New/Open. A Plan→Design re-push brings new lines → the signature diverges → red.
  const [optimizePush, setOptimizePush] = useState(null);

  const onDesignShearWalls = (byFloor, shape) => {
    setDesignLinesByFloor(byFloor);
    setDesignShape(shape);
    const allIds = new Set();
    Object.values(byFloor).forEach(arr => (arr||[]).forEach(ln => allIds.add(ln.id)));
    setSegsByLine(prev => {
      const next = {};
      allIds.forEach(id => { next[id] = prev[id] || []; });   // keep layouts for unchanged lines (shared across floors)
      return next;
    });
    const act = byFloor[activeFloor] || byFloor[1] || byFloor[2] || [];
    setSelLine(prev => act.find(l=>l.id===prev) ? prev : (act[0] ? act[0].id : null));
    setDesignStale(false);                          // a fresh handoff always yields geometry-complete lines
    setTab("design");
  };
  // ── PROJECT FILES (.wps = JSON: sketcher + design + calc, versioned) ──
  const projectRef = useRef(null);                       // sketcher get/set, registered below
  const fileInputRef = useRef(null);
  const registerProject = useCallback((api)=>{ projectRef.current=api; },[]);
  const [projectName, setProjectName] = useState("Untitled");   // (rev 70) editable name → save filename, round-trips in .wps
  const [lastSaved, setLastSaved] = useState(null);             // (rev 70) ms timestamp of last save (or the loaded file's savedAt)
  const onSave = useCallback(()=>{
    const sk = projectRef.current ? projectRef.current.get() : null;
    const now = new Date();
    const proj = { app:"plan-sketcher-suite", version:CURRENT_VERSION, savedAt:now.toISOString(), name:projectName,
                   sketcher:sk, design:{ linesByFloor:designLinesByFloor, shape:designShape, segsByLine, d, selLine },
                   // calc.tabs is the rev-132 sub-tab model; calc.segments is kept (= active tab) so a
                   // pre-132 build can still open the file and show at least the active wall.
                   calc:{ g, segments, tabs:calcTabs, activeCalcId }, ui:{ tab, hlSel, twoStory, activeFloor } };
    const blob = new Blob([JSON.stringify(proj,null,1)], {type:"application/json"});
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    const fname = (projectName||"").trim().replace(/[^\w.\- ]+/g,"_").replace(/\s+/g,"-") || "plan-project";
    a.download = fname.toLowerCase().endsWith(".wps") ? fname : fname + ".wps";
    a.click();
    URL.revokeObjectURL(a.href);
    setLastSaved(now.getTime());                                // (rev 70) update the "Saved …" status
  },[designLinesByFloor, designShape, segsByLine, d, g, segments, calcTabs, activeCalcId, tab, hlSel, selLine, twoStory, activeFloor, projectName]);
  const onOpen = useCallback(()=>{ fileInputRef.current && fileInputRef.current.click(); },[]);
  const onFileChosen = useCallback((e)=>{
    const f = e.target.files && e.target.files[0];
    e.target.value = "";                                  // allow re-opening the same file
    if(!f) return;
    const rd = new FileReader();
    rd.onload = ()=>{
      try{
        const raw = JSON.parse(rd.result);
        if(raw.app!=="plan-sketcher-suite") throw new Error("not a plan-sketcher-suite project");
        const L = loadProject(raw);                       // version ladder + merge-onto-defaults
        if(L.newer) window.alert("This project was saved by a newer version of the app — some data may not load correctly.");
        const p = L.project;                              // migrated project (version stamped up)
        if(p.sketcher && projectRef.current) projectRef.current.set(p.sketcher);
        if(p.design){ setDesignLinesByFloor(L.design.linesByFloor); setDesignShape(L.design.shape);
                      setSegsByLine(L.design.segsByLine); if(L.design.d) setD(L.design.d);
                      setSelLine(L.design.selLine); }
        if(p.calc){ if(L.calc.g) setG(L.calc.g);
                    if(L.calc.tabs){                       // rev 132: restore the sub-tab set
                      setCalcTabs(L.calc.tabs);
                      setActiveCalcId(L.calc.activeCalcId);
                      // reseed the id counter past any loaded "calc-N" so new tabs can't collide
                      let mx = 1; L.calc.tabs.forEach(t => { const m = /calc-(\d+)/.exec(t.id||""); if(m) mx = Math.max(mx, +m[1]); });
                      calcSeq.current = mx + 1;
                      setHlSel(null);
                    } else if(L.calc.segments) setSegments(L.calc.segments); }
        setDesignStale(L.design.stale);                   // rev 24: flag if any saved line lacked geometry
        setCalcPush(null);                                // rev 130: a loaded file's calc sheet is in sync; re-arms on the next send
        setOptimizePush(null);                            // rev 130b: a loaded file's design is in sync; re-arms on the next Optimize
        // v2 drops you back where you left; v1 files (no ui slice) open on the Plan tab as before
        setHlSel(L.ui.hlSel);
        setTwoStory(L.ui.twoStory);
        setActiveFloor(L.ui.activeFloor);
        setTab(L.ui.tab);
        setProjectName(typeof raw.name==="string" && raw.name.trim() ? raw.name : "Untitled");   // (rev 70)
        setLastSaved(raw.savedAt ? (Date.parse(raw.savedAt)||null) : null);                       // (rev 70) show the file's own save time
      }catch(err){ window.alert("Could not open project: "+err.message); }
    };
    rd.readAsText(f);
  },[]);
  const onNew = useCallback(()=>{
    if(!window.confirm("Start a new project? Unsaved work will be lost.")) return;
    if(projectRef.current) projectRef.current.set({ graph:{nodes:[],edges:[]}, wallProps:{},
      noSupport:[], sections:{h:null,v:null}, nextId:0 });
    setDesignLinesByFloor({}); setDesignShape(null); setSegsByLine({}); setDesignStale(false);
    setCalcPush(null);                              // rev 130: clear stale-calc memory on New
    setOptimizePush(null);                          // rev 130b: clear stale-optimize memory on New
    setTwoStory(false); setActiveFloor(1);
    setProjectName("Untitled"); setLastSaved(null);   // (rev 70) fresh project → fresh name + no save time
  },[]);
  // rev 24: the Design-tab stale banner rebuilds geometry-less lines from the restored plan. If the
  // saved plan still has a wind reaction, regenerate straight from it (rerun → onDesignShearWalls,
  // which clears stale); otherwise send the user to the Plan to place a cut.
  const onRebuildDesign = useCallback(()=>{
    const api = projectRef.current;
    if(api && api.hasReactions && api.rerun){ api.rerun(); }
    else { setTab("plan"); window.alert("This plan has no wind reaction yet. On the Plan, drag a wind section across the building and mark the point-load walls, then press “Design shear walls”."); }
  },[]);
  const fileOps = useMemo(()=>({onSave,onOpen,onNew}),[onSave,onOpen,onNew]);

  const ovSet = (lineId, idx, key, val) =>
    setSegsByLine(prev => ({ ...prev, [lineId]: prev[lineId].map((s,j)=> j!==idx ? s :
      key===null ? { start:s.start, length:s.length } : { ...s, ov:{ ...(s.ov||{}), [key]:val||undefined } }) }));

  // Design → calc sheet: this line's segments + force become a SUB-TAB. Pushing a line the sheet
  // already has (matched by `line.id`) UPDATES that tab in place (current optimized design + force +
  // name + marks); a new line opens a new tab. `name`/`marks` come from the Design tab so the sub-tab
  // title and the per-segment SW-marks read identically across both tabs. (rev 132)
  const applyToCalc = (line, segs, res, dC, name, marks) => {
    const next = Array.from({ length: 6 }, (_, i) => ({
      length: segs[i] ? segs[i].length : 0,
      // (rev 49) send THIS line's per-wall/per-floor DL trib to the calc sheet (was the global dC.*);
      // every sent segment seeds with it, still editable per-segment on the sheet afterward.
      height: line.heightFt, roofTrib: line.roofTrib ?? dC.roofTrib, floorTrib: line.floorTrib ?? dC.floorTrib,
      hdDist: dC.hdDist, thickness: dC.thickness, anchor: dC.anchor,
      selType: res[i] && isNum(res[i].selType) ? Math.min(res[i].selType, 6) : 1,
      ftgWidth: dC.ftgWidth, ftgThick: dC.ftgThick,
    }));
    const wWind = Math.round(line.forceLbs);
    const tabName = name || `${line.windAxis === "h" ? "E–W" : "N–S"} · ${fmt(line.forceLbs/1000,2)}k · ${fmt(line.lengthFt,0)}′`;
    const marksArr = Array.isArray(marks) ? marks : null;
    const existing = calcTabs.find((t) => t.lineId === line.id);
    if (existing) {
      setCalcTabs((prev) => prev.map((t) => t.id === existing.id
        ? { ...t, name:tabName, marks:marksArr, segments:next, wWind } : t));
      selectCalcTab(existing.id);
    } else {
      const id = newCalcId();
      setCalcTabs((prev) => [...prev, { id, name:tabName, lineId:line.id, marks:marksArr, segments:next, wWind }]);
      selectCalcTab(id);
    }
    setCalcPush({ lineId: line.id, sig: calcPushSig(line, segs, res, dC) });   // rev 130: remember what this push produced
    setTab("calc");
  };

  // Pinned-ribbon support: measure the sticky tab bar's height into a CSS var so the
  // sketcher ribbon can stick exactly below it (fallback 42px in the .ribbon rule).
  const tabBarRef = useRef(null);
  useEffect(() => {
    const setH = () => {
      if (tabBarRef.current)
        document.documentElement.style.setProperty("--tabbar-h", tabBarRef.current.offsetHeight + "px");
    };
    setH();
    window.addEventListener("resize", setH);
    return () => window.removeEventListener("resize", setH);
  }, []);

  const SHEET_NO = { plan:"S-1", design:"S-2", calc:"S-3" };
  const tabBtn = (id, label, dot) => (
    <button onClick={() => setTab(id)} className="ttab"
      style={{ display:"flex", alignItems:"center", gap:7,
               padding:"8px 22px 10px", fontSize:12, fontWeight:700, letterSpacing:"0.1em", textTransform:"uppercase",
               border:"none", borderBottom: tab===id ? `3px solid ${SW.accent}` : "3px solid transparent",
               background: tab===id ? SW.accentSoft : "transparent",
               color: tab===id ? SW.accent : SW.faint, cursor:"pointer" }}>
      <span><span className="teye">{SHEET_NO[id]}</span>{label}</span>
      {dot !== undefined && (
        <span style={{ width:8, height:8, borderRadius:99, background: dot ? SW.green : SW.red, display:"inline-block" }}
              title={dot ? "All walls pass" : "Walls failing"} />
      )}
    </button>
  );

  // ── DARK SHEET — Design tab only (styling unchanged) ──
  const designSheet = (
    <div className="paper-desk sw-root" style={{ minHeight:"calc(100vh - 46px)", color:SW.ink, fontFamily:"'IBM Plex Sans','Helvetica Neue',Arial,sans-serif", padding:"20px 14px" }}>
      <div style={{ maxWidth:1100, margin:"0 auto", background:SW.sheet, border:`1.5px solid ${SW.ink}`, boxShadow:"0 1px 1px rgba(28,39,51,.04), 0 10px 24px -14px rgba(28,39,51,.30), 4px 4px 0 rgba(28,39,51,.10)" }}>
        {/* title block */}
        <div style={{ display:"flex", flexWrap:"wrap", borderBottom:`1.5px solid ${SW.ink}` }}>
          <div style={{ flex:"2 1 320px", padding:"16px 20px", borderRight:`1px solid ${SW.rule}` }}>
            <div style={{ fontSize:10, letterSpacing:"0.2em", color:SW.faint, textTransform:"uppercase" }}>Structural Calculation</div>
            <h1 style={{ margin:"4px 0 2px", fontSize:22, fontWeight:800, letterSpacing:"0.01em", color:SW.ink }}>
              Plywood Shear Walls{g.grade === "str1" ? " (Structural I)" : ""} <span style={{ fontWeight:400, color:SW.faint }}>w/ Wood Studs</span>
            </h1>
            <div style={{ fontSize:11, fontFamily:MONO, color:SW.accent }}>{CODES[g.code]} · Basic Load Combinations</div>
          </div>
          <div style={{ flex:"1 1 160px", padding:"16px 20px", borderRight:`1px solid ${SW.rule}` }}>
            <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:SW.faint, display:"block", marginBottom:4 }}>Building code</label>
            <select value={g.code} onChange={(e)=>setGl("code",+e.target.value)} style={{ ...selStyle, width:"100%" }}>
              <option value={1}>2006 IBC</option><option value={2}>2009 IBC</option>
              <option value={3}>2012 IBC</option><option value={4}>2015 IBC</option>
            </select>
            <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:SW.faint, display:"block", margin:"10px 0 4px" }}>Wood framing</label>
            <select value={g.species} onChange={(e)=>setGl("species",+e.target.value)} style={{ ...selStyle, width:"100%" }}>
              <option value={1}>Southern Pine</option><option value={2}>Douglas-Fir</option>
            </select>
          </div>
          <div style={{ flex:"0 1 120px", padding:"16px 20px" }}>
            <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:SW.faint, display:"block", marginBottom:4 }}>Shear line</label>
            <input value={g.line} onChange={(e)=>setGl("line",e.target.value)}
              style={{ width:60, padding:"4px 8px", border:`1px solid ${SW.rule}`, borderRadius:4, fontFamily:MONO, fontSize:18,
                       fontWeight:700, textAlign:"center", color:SW.accent, background:SW.input, outline:"none" }} />
          </div>
        </div>
        <div style={{ padding:"8px 20px 28px" }}>
          <DesignTab g={g} shape={designShape} lines={designLines} linesByFloor={designLinesByFloor}
                     wTotal={wTotal}
                     segsByLine={segsByLine} setSegsByLine={setSegsByLine} ovSet={ovSet}
                     d={d} setDk={setDk} applyToCalc={applyToCalc} setGl={setGl}
                     selLine={selLine} setSelLine={setSelLine}
                     twoStory={twoStory} activeFloor={activeFloor} setActiveFloor={setActiveFloor}
                     stale={designStale} onRebuild={onRebuildDesign} calcPush={calcPush}
                     optimizePush={optimizePush} setOptimizePush={setOptimizePush}/>
          <div style={{ marginTop:24, fontSize:10, color:SW.faint, lineHeight:1.6, borderTop:`1px solid ${SW.rule}`, paddingTop:10 }}>
            Faithful port of the source spreadsheet, including its exact formulas and thresholds (e.g. the wind end-post compression denominator and uplift &lt; 625 lbs → "neglect"). The Design tab optimizer verifies every candidate through this same engine. Allowable values per the embedded schedule; holdowns/anchors per Simpson HDU / SSTB / STHD / MST capacities tabulated in the workbook. END OF CALC.
          </div>
        </div>
      </div>
    </div>
  );

  // ── LIGHT SHEET — Calculation Sheet, 1:1 with the standalone calculator ──
  // rev 132 — Chrome-style sub-tab bar for the Calculation Sheet. One tab per shear-wall line (or
  // manual calc). rev 54: pinned via sticky INSIDE the tall page wrapper (which also holds the sheet),
  // so it stays visible the whole way down the page — mirroring the Plan Sketcher ribbon.
  const calcTabBar = (
    <div className="no-print" style={{ position:"sticky", top:"var(--tabbar-h,42px)", zIndex:35,
                  display:"flex", alignItems:"flex-end", gap:4, padding:"6px 2px 0",
                  background:LT.paper, borderBottom:`1px solid ${LT.rule}`, overflowX:"auto" }}>
        {calcTabs.map((t) => {
          const active = t.id === activeCalcId;
          const editing = editingCalcId === t.id;
          const st = calcTabStatus[t.id];
          const dot = st === "ok" ? LT.green : st === "fail" ? LT.red : LT.faint;
          return (
            <div key={t.id} className={"calctab" + (active ? " is-active" : "")}
              onClick={() => !editing && selectCalcTab(t.id)} onDoubleClick={() => startRenameCalc(t.id)}
              title={editing ? "" : (t.lineId ? "Sent from the Design tab — re-send that line to update this tab" : "Custom calc — double-click to rename")}
              style={{ display:"flex", alignItems:"center", gap:7, cursor: editing ? "text" : "pointer", flex:"0 0 auto",
                       padding:"7px 8px 8px 12px", maxWidth:260, marginBottom:-1,
                       border:`1px solid ${LT.rule}`, borderBottom:`1px solid ${active ? LT.sheet : LT.rule}`,
                       borderTopLeftRadius:9, borderTopRightRadius:9,
                       background: active ? LT.sheet : LT.zebra, color: active ? LT.ink : LT.faint,
                       fontFamily:MONO, fontSize:11.5, fontWeight: active ? 700 : 500, whiteSpace:"nowrap",
                       boxShadow: active ? `inset 0 2px 0 ${LT.blue}` : "none" }}>
              <span style={{ width:7, height:7, borderRadius:"50%", background:dot, flex:"0 0 auto" }}
                    title={st === "ok" ? "All walls pass" : st === "fail" ? "Has a failing wall" : "No wall sized yet"} />
              {editing ? (
                <input autoFocus value={editName}
                  onClick={(e) => e.stopPropagation()} onPointerDown={(e) => e.stopPropagation()}
                  onChange={(e) => setEditName(e.target.value)}
                  onBlur={commitRenameCalc}
                  onKeyDown={(e) => { if (e.key === "Enter") commitRenameCalc(); else if (e.key === "Escape") cancelRenameCalc(); }}
                  style={{ width:Math.max(80, Math.min(220, editName.length*7+24)), fontFamily:MONO, fontSize:11.5,
                           fontWeight:700, color:LT.ink, border:`1px solid ${LT.blue}`, borderRadius:4,
                           padding:"1px 4px", outline:"none", background:"#FFF" }} />
              ) : (
                <span style={{ overflow:"hidden", textOverflow:"ellipsis" }}>{t.name}</span>
              )}
              {calcTabs.length > 1 && !editing && (
                <button className="calctab-x" onClick={(e) => { e.stopPropagation(); closeCalcTab(t.id); }}
                  title="Close this calc" aria-label="Close tab"
                  style={{ border:"none", background:"none", cursor:"pointer", color:LT.faint, fontSize:15,
                           lineHeight:1, padding:"0 3px", borderRadius:4, flex:"0 0 auto" }}>×</button>
              )}
            </div>
          );
        })}
        <button className="calc-add" onClick={addCalcTab} aria-label="Add calculation tab"
          title="New blank calculation (run a wall independently of the Design tab)"
          style={{ display:"flex", alignItems:"center", justifyContent:"center", flex:"0 0 auto",
                   width:30, height:30, marginBottom:4, marginLeft:2, border:"none", borderRadius:7,
                   background:"transparent", color:LT.blue, fontSize:21, lineHeight:1, cursor:"pointer" }}>+</button>
    </div>
  );

  const calcSheetPage = (
    <div className="paper-desk lt-root" style={{ minHeight:"calc(100vh - 46px)", color:LT.ink, fontFamily:"'IBM Plex Sans','Helvetica Neue',Arial,sans-serif", padding:"10px 16px 24px" }}>
      <div style={{ maxWidth:1100, margin:"0 auto" }}>
      {calcTabBar}
      <div style={{ background:LT.sheet, border:`1.5px solid ${LT.ink}`, boxShadow:"0 1px 1px rgba(28,39,51,.04), 0 10px 24px -14px rgba(28,39,51,.30), 4px 4px 0 rgba(28,39,51,.10)" }}>
        {/* ===== TITLE BLOCK ===== */}
        <div style={{ display:"flex", flexWrap:"wrap", borderBottom:`1.5px solid ${LT.ink}` }}>
          <div style={{ flex:"2 1 320px", padding:"16px 20px", borderRight:`1px solid ${LT.rule}` }}>
            <div style={{ fontSize:10, letterSpacing:"0.2em", color:LT.faint, textTransform:"uppercase" }}>Structural Calculation</div>
            <h1 style={{ margin:"4px 0 2px", fontSize:22, fontWeight:800, letterSpacing:"0.01em", color:LT.ink }}>
              Plywood Shear Walls{g.grade === "str1" ? " (Structural I)" : ""} <span style={{ fontWeight:400, color:LT.faint }}>w/ Wood Studs</span>
            </h1>
            <div style={{ fontSize:11, fontFamily:MONO, color:LT.blue }}>{CODES[g.code]} · Basic Load Combinations</div>
          </div>
          <div style={{ flex:"1 1 160px", padding:"16px 20px", borderRight:`1px solid ${LT.rule}` }}>
            <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:LT.faint, display:"block", marginBottom:4 }}>Building code</label>
            <select value={g.code} onChange={(e)=>setGl("code",+e.target.value)} style={{ ...ltSel, width:"100%" }}>
              <option value={1}>2006 IBC</option><option value={2}>2009 IBC</option>
              <option value={3}>2012 IBC</option><option value={4}>2015 IBC</option>
            </select>
            <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:LT.faint, display:"block", margin:"10px 0 4px" }}>Wood framing</label>
            <select value={g.species} onChange={(e)=>setGl("species",+e.target.value)} style={{ ...ltSel, width:"100%" }}>
              <option value={1}>Southern Pine</option><option value={2}>Douglas-Fir</option>
            </select>
          </div>
          <div style={{ flex:"0 1 150px", padding:"16px 20px", display:"flex", flexDirection:"column", gap:8 }}>
            <div>
              <label style={{ fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase", color:LT.faint, display:"block", marginBottom:4 }}>Shear line</label>
              <input value={g.line} onChange={(e)=>setGl("line",e.target.value)}
                style={{ width:60, padding:"4px 8px", border:`1px solid ${LT.rule}`, borderRadius:4, fontFamily:MONO, fontSize:18, fontWeight:700, textAlign:"center", color:LT.blue, background:"#FDFDFB", outline:"none" }} />
            </div>
            <button className="no-print" onClick={()=>window.print()}
              style={{ alignSelf:"flex-start", padding:"5px 12px", fontSize:11, fontWeight:700, letterSpacing:"0.06em", border:`1.5px solid ${LT.blue}`, background:LT.blue, color:"#FFFFFF", cursor:"pointer", borderRadius:4 }}>
              ⎙ Print report
            </button>
          </div>
        </div>
        <div style={{ padding:"8px 20px 28px" }}>
          <HL.Provider value={{ sel: hlSel, setSel: setHlSel }}>
            <CalcSheet g={gEff} setGl={setGlCalc} segments={segments} setSegments={setSegments} results={resultsU} totalL={totalL} marks={calcMarks}/>
          </HL.Provider>
          <div style={{ marginTop:24, fontSize:10, color:LT.faint, lineHeight:1.6, borderTop:`1px solid ${LT.rule}`, paddingTop:10 }}>
            Faithful port of the source spreadsheet, including its exact formulas and thresholds (e.g. the wind end-post compression denominator and uplift &lt; 625 lbs → "neglect"). Hover a row label for its source-cell reference. The Design tab optimizer verifies every candidate through this same engine. Allowable values per the embedded schedule; holdowns/anchors per Simpson HDU / SSTB / STHD / MST capacities tabulated in the workbook. END OF CALC.
          </div>
        </div>
      </div>
      </div>
    </div>
  );

  return (
    <div className="paper-desk" style={{ minHeight:"100vh" }}>
      <style>{LT_CSS}</style>
      {/* tab bar */}
      <style>{APP_CSS}</style>
      {/* persistent app-level header: file toolbar (rev 69) + suite tab bar, in ONE sticky wrapper so
          New/Open/Save are reachable from every tab and the Plan ribbon / Design constraints stick below
          the WHOLE header (tabBarRef now measures the wrapper, so --tabbar-h includes the file bar). */}
      <div ref={tabBarRef} className="no-print apphdr" style={{ position:"sticky", top:0, zIndex:40 }}>
        <div className="filebar">
          <div className="fblabel">Project</div>
          <input className="fbname" value={projectName} spellCheck={false}
                 onChange={e=>setProjectName(e.target.value)}
                 placeholder="Untitled" title="Project name — used as the saved file name"/>
          <button className="filebtn" title="New project" onClick={onNew}>🗋 New</button>
          <button className="filebtn" title="Open project (Ctrl+O)" onClick={onOpen}>📂 Open</button>
          <button className="filebtn" title="Save project (Ctrl+S)" onClick={onSave}>💾 Save</button>
          <div className="fbsep"/>
          <button className="filebtn" title="Undo (Ctrl+Z)" onClick={()=>projectRef.current&&projectRef.current.undo&&projectRef.current.undo()}>↶ Undo</button>
          <button className="filebtn" title="Redo (Ctrl+Y / Ctrl+Shift+Z)" onClick={()=>projectRef.current&&projectRef.current.redo&&projectRef.current.redo()}>↷ Redo</button>
          <div className="fbstatus" title={lastSaved!=null ? new Date(lastSaved).toLocaleString() : "This project has not been saved yet"}>
            {(()=>{ if(lastSaved==null) return "Not saved yet";
                    const d=new Date(lastSaved), now=new Date();
                    const t=d.toLocaleTimeString([], {hour:"numeric", minute:"2-digit"});
                    const sameDay = d.toDateString()===now.toDateString();
                    return "Saved "+(sameDay ? t : d.toLocaleDateString([], {month:"short", day:"numeric"})+", "+t); })()}
          </div>
        </div>
        <div className="tbar" style={{ display:"flex", alignItems:"center", borderBottom:`1px solid ${SW.rule}`, background:SW.sheet }}>
          <div className="tbrand" style={{ padding:"6px 16px" }}>
            <div style={{ fontSize:12, fontWeight:800, letterSpacing:"0.06em", color:SW.ink }}>
              PLAN<span style={{color:SW.accent}}>·</span>SKETCHER <span style={{color:SW.faint,fontWeight:400}}>+ Shear Walls</span>
            </div>
            <small>STRUCTURAL SUITE</small>
          </div>
          {tabBtn("plan","Plan Sketcher")}
          {tabBtn("design","Design")}
          {tabBtn("calc","Calculation Sheet", actU.length ? calcOK : undefined)}
          <div style={{ marginLeft:"auto", padding:"6px 16px", fontFamily:MONO, fontSize:11, fontWeight:700,
                        letterSpacing:"0.08em", color:SW.faint, whiteSpace:"nowrap" }}
               title="App version">
            Version {APP_VERSION}
          </div>
        </div>
      </div>
      {/* keep the sketcher mounted so the plan survives tab switches */}
      <input ref={fileInputRef} type="file" accept=".wps,.json" style={{display:"none"}} onChange={onFileChosen}/>
      <div style={{ display: tab==="plan" ? "block" : "none" }}>
        <PlanSketcher onDesignShearWalls={onDesignShearWalls} fileOps={fileOps} registerProject={registerProject}
                      twoStory={twoStory} setTwoStory={setTwoStory} activeFloor={activeFloor} setActiveFloor={setActiveFloor}
                      g={g} setGl={setGl} setWtotal={setWtotal}/>
      </div>
      {tab === "design" && designSheet}
      {tab === "calc" && calcSheetPage}
    </div>
  );
}
