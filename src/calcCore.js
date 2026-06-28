/* ════════════════════════════════════════════════════════════════════════
   calcCore.js — PLYWOOD SHEAR WALL CALCULATION ENGINE
   Extracted verbatim from plan-sketcher-suite.jsx (rev 33 split; behavior
   byte-identical). This is the guarded engine: a faithful port of
   "Plywood Shear Wall - Wood Studs.xlsx" (+ Structural I schedule). Do NOT
   change any formula here without the user's explicit approval — the engine
   byte-identity guard diffs these functions against a baseline.

   SANCTIONED DEVIATIONS (user-approved; the guard for the affected fn is
   golden-OUTPUT, not byte-identity, and its baseline was re-snapshotted):
     • rev 61 — calcSegment: E_seis dropped its /R, so vSeismic is now the
       post-R (ASCE 7 reduced) seismic base shear, parallel to wWind; the
       engine applies only the 0.7 ASD factor. g.R is no longer read here.
     • rev 65 — DOUBLE-SIDED shear walls (marks 4–6): SCHEDULE/SCHEDULE_STR1
       gain three derived rows = the single-sided rows with 2× wind, 2×
       seismic, 2× Ga and the "BOTH SIDES OF WALL" callout; NAIL_EDGE gains
       4/5/6; calcSegment's sugS/sugW/allowS ladders + the deflection Ga
       index extend to 6 marks; generateDesign now treats 4–6 as a LAST
       RESORT (single-sided 1–3 is searched first; doubles only if nothing
       single-sided passes). For any demand a single-sided design satisfies,
       calcSegment AND generateDesign are OUTPUT-identical to the rev-64
       engine — the new marks change output only above single-sided capacity
       (where the engine previously returned "FAILED!!!"). Single-sided rows
       1–3 are byte-identical to the verbatim source.

   Self-contained: depends only on Math + the helpers defined in this file
   (no React, no geometry/sketcher imports), so there is no circular
   dependency with the app file that imports from it.

   Exports (consumed by plan-sketcher-suite.jsx): calcSegment, generateDesign,
   baseDesignSeg, schedFor, HD_TABLE, NAIL_EDGE, CODES, isNum, xMax, numOr0.
   Also exported for the test harness / future modules: CP, evaluateCandidate,
   SCHEDULE, SCHEDULE_STR1.
   ════════════════════════════════════════════════════════════════════════ */

// Sheathing-grade schedules. SCHEDULE (rated) = original "Plywood Shear Wall - Wood Studs.xlsx";
// SCHEDULE_STR1 extracted verbatim from "shear_walls_-_Structural_1.xlsx" (formula-identical workbook,
// only Shearwall Schedule capacities + Ga differ). Nailing/anchorage callouts identical between grades.
// Single-sided base rows (marks 1–3) — extracted verbatim from the source workbooks; DO NOT edit values.
const SCHEDULE_1S = [
  { mark: 1, sheathing: '1/2" WOOD STR. PANELS — ONE SIDE OF WALL', edge: '10d COMMON AT 6" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 36" O.C.', wood: '16d STAGGERED AT 6" O.C.', wind: 435, seismic: 310, ga: 14 * 1.2 },
  { mark: 2, sheathing: '1/2" WOOD STR. PANELS — ONE SIDE OF WALL', edge: '10d COMMON AT 4" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 24" O.C.', wood: '16d STAGGERED AT 4" O.C.', wind: 645, seismic: 460, ga: 17 * 1.2 },
  { mark: 3, sheathing: '1/2" WOOD STR. PANELS — ONE SIDE OF WALL', edge: '10d COMMON AT 3" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 18" O.C.', wood: '16d STAGGERED AT 3" O.C.', wind: 840, seismic: 600, ga: 19 * 1.2 },
];
const SCHEDULE_STR1_1S = [
  { mark: 1, sheathing: '1/2" WOOD STR. PANELS-STR. 1 — ONE SIDE OF WALL', edge: '10d COMMON AT 6" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 36" O.C.', wood: '16d STAGGERED AT 6" O.C.', wind: 475, seismic: 340, ga: 16 * 1.2 },
  { mark: 2, sheathing: '1/2" WOOD STR. PANELS-STR. 1 — ONE SIDE OF WALL', edge: '10d COMMON AT 4" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 24" O.C.', wood: '16d STAGGERED AT 4" O.C.', wind: 715, seismic: 510, ga: 20 * 1.2 },
  { mark: 3, sheathing: '1/2" WOOD STR. PANELS-STR. 1 — ONE SIDE OF WALL', edge: '10d COMMON AT 3" O.C.', field: '10d COMMON AT 12" O.C.', concrete: '1/2" DIA. A.B. AT 18" O.C.', wood: '16d STAGGERED AT 3" O.C.', wind: 930, seismic: 665, ga: 22 * 1.2 },
];
// DOUBLE-SIDED variant (user-sanctioned addition): sheathe BOTH faces with the same panel/nailing.
// Shear capacity is EXACTLY 2× the single-sided counterpart (wind & seismic both ×2); the apparent
// shear stiffness Ga is also 2× (combined two-sided value per SDPWS 4.3.3.4 — affects deflection only,
// not capacity). Identical edge/field/anchorage callouts, applied each side. Marks are 4/5/6 = the
// double of 1/2/3. Derived from the single-sided rows so the ×2 can never drift out of sync.
const dblSide = (t, mark) => ({ ...t, mark,
  sheathing: t.sheathing.replace("ONE SIDE OF WALL", "BOTH SIDES OF WALL"),
  wind: t.wind * 2, seismic: t.seismic * 2, ga: t.ga * 2, doubleSided: true });
const withDbl = (rows) => [ ...rows, dblSide(rows[0], 4), dblSide(rows[1], 5), dblSide(rows[2], 6) ];
// Full 6-mark schedules (1–3 single-sided, 4–6 double-sided). Single-sided rows are byte-identical
// to the verbatim source; the optimizer treats 4–6 as a LAST RESORT (see generateDesign).
const SCHEDULE = withDbl(SCHEDULE_1S);
const SCHEDULE_STR1 = withDbl(SCHEDULE_STR1_1S);
// grade ∈ {"rated","str1"}; absent/unknown → rated (backward-compatible with v1 .wps files)
const schedFor = (grade) => (grade === "str1" ? SCHEDULE_STR1 : SCHEDULE);
// compact edge-nailing callouts per schedule mark (keep in sync with SCHEDULE above).
// 4/5/6 mirror 1/2/3 with a "(2 sides)" suffix — same nailing applied to both faces.
const NAIL_EDGE = { 1: '10d-6" o.c. @ edges', 2: '10d-4" o.c. @ edges', 3: '10d-3" o.c. @ edges',
                    4: '10d-6" o.c. @ edges (2 sides)', 5: '10d-4" o.c. @ edges (2 sides)', 6: '10d-3" o.c. @ edges (2 sides)' };
const CODES = { 1:"2006 INTERNATIONAL BUILDING CODE (IBC)", 2:"2009 INTERNATIONAL BUILDING CODE (IBC)", 3:"2012 INTERNATIONAL BUILDING CODE (IBC)", 4:"2015 INTERNATIONAL BUILDING CODE (IBC)" };
const HD_TABLE = [
  { name:"HDU2", cap:3075 }, { name:"HDU4", cap:4565 }, { name:"HDU5", cap:5645 },
  { name:"HDU8", cap:7870 }, { name:"HDU11", cap:9335 }, { name:"HDU14", cap:14445 },
];

const isNum = (v) => typeof v === "number" && isFinite(v);
const xMax = (...vals) => { const n = vals.filter(isNum); return n.length ? Math.max(...n) : 0; };
const numOr0 = (v) => (isNum(v) ? v : 0);
const CP = (FcE, Fc) => { const r = FcE/Fc; const phi=(1+r)/2/0.8; return phi - Math.sqrt(phi*phi - r/0.8); };

// ---------- Core calculation (one segment) — verbatim port ----------
function calcSegment(seg, g, totalL) {
  const SCHED = schedFor(g.grade); // sheathing grade: rated (default) or Structural I — values only, formulas identical
  const L = seg.length, h = seg.height;
  if (!(L > 0)) return { active: false };
  const sp = g.species === 1;
  const E_seis = 0.7 * g.vSeismic;  // rev 61 (sanctioned): /R dropped — vSeismic is now the post-R (ASCE 7 reduced) seismic base shear, parallel to wWind; engine applies ONLY the 0.7 ASD factor. g.R is no longer used by the engine.
  const F_wind = g.code >= 3 ? 0.6 * g.wWind : g.wWind;
  const aspect = h / L;
  const aspectNG = aspect > 3.5;
  const wdl = seg.roofTrib * g.roofDL + seg.floorTrib * g.floorDL + g.wallDL * h;
  // SEISMIC
  const Fs = (E_seis * L) / totalL;
  const vS = Fs / L;
  const factor = aspectNG || aspect >= 2 ? (2 * L) / h : 1;
  // Capacity ladder is 6 marks: 1–3 single-sided, 4–6 double-sided (2× the single capacity). Because
  // 2×(mark 1) ≥ mark 3 in every schedule, the ladder is monotonic and 4–6 are only reached once 1–3
  // are exceeded — output is byte-identical to the old 3-mark engine for any demand ≤ mark-3 capacity.
  const sV = SCHED.map((t) => t.seismic);
  const allowS = vS <= factor*sV[0] ? factor*sV[0] : vS <= factor*sV[1] ? factor*sV[1] : vS <= factor*sV[2] ? factor*sV[2]
               : vS <= factor*sV[3] ? factor*sV[3] : vS <= factor*sV[4] ? factor*sV[4] : vS <= factor*sV[5] ? factor*sV[5] : "FAILED!!!";
  const sugS = aspectNG ? "None"
             : vS <= factor*sV[0] ? 1 : vS <= factor*sV[1] ? 2 : vS <= factor*sV[2] ? 3
             : vS <= factor*sV[3] ? 4 : vS <= factor*sV[4] ? 5 : vS <= factor*sV[5] ? 6 : "FAILED!!!";
  const MotS = Fs * h;
  const A = 1 + 0.14 * g.sds;
  const AwDL = A * wdl;
  const compS = (MotS + AwDL * L * Math.min(3, L / 2)) / (L - (1.5 + seg.hdDist) / 12);
  const B = 0.6 - 0.14 * g.sds;
  const BwDL = B * wdl;
  const upliftFn = (Mot, w, denomIn) => { const u = (Mot - w*L*(L/2 - 1.5/12)) / (L - denomIn/12); return u < 0 ? 0 : u < 625 ? "neglect" : u; };
  const upHD_S = upliftFn(MotS, BwDL, 1.5 + seg.hdDist);
  const upStrap_S = upliftFn(MotS, BwDL, 3);
  // WIND
  const Fw = (F_wind * L) / totalL;
  const vW = Fw / L;
  const wV = SCHED.map((t) => t.wind);
  const sugW = aspectNG ? "None"
             : vW <= wV[0] ? 1 : vW <= wV[1] ? 2 : vW <= wV[2] ? 3
             : vW <= wV[3] ? 4 : vW <= wV[4] ? 5 : vW <= wV[5] ? 6 : "FAILED!!!";
  const MotW = Fw * h;
  const compW = (MotW + wdl * L * Math.min(3, L / 2)) / (L - (1.5 + seg.hdDist / 12) / 12); // E42 quirk preserved
  const Cfac = 0.6;
  const CwDL = Cfac * wdl;
  const upHD_W = upliftFn(MotW, CwDL, 1.5 + seg.hdDist);
  const upStrap_W = upliftFn(MotW, CwDL, 3);
  // END POSTS
  const maxComp = xMax(compS, compW);
  const t = seg.thickness;
  const Cf = t === 3.5 ? 1.15 : t === 5.5 ? 1.1 : t === 7.25 ? 1.05 : 1;
  const FcE1 = (0.822 * (sp ? 510000 : 580000)) / Math.pow((h * 12) / t, 2);
  const Fc1 = (sp ? 1400 : 1350) * 1.6 * Cf;
  const cp1 = CP(FcE1, Fc1);
  const Pa224 = 2 * 1.5 * 3.5 * Fc1 * cp1;
  const Pa44 = 3.5 * 3.5 * Fc1 * cp1;
  const Pa226 = 2 * 1.5 * 5.5 * Fc1 * cp1;
  const Pa46 = 3.5 * 5.5 * Fc1 * cp1;
  const FcE2 = (0.822 * (sp ? 550000 : 470000)) / Math.pow((h * 12) / t, 2);
  const Fc2 = (sp ? 825 : 700) * 1.6;
  const cp2 = CP(FcE2, Fc2);
  const Pa66 = 5.5 * 5.5 * Fc2 * cp2;
  const Pa68 = 5.5 * 7.5 * Fc2 * cp2;
  const post =
    t <= 4
      ? maxComp <= Pa224 ? "(2) 2x4" : maxComp <= Pa44 ? "4x4" : maxComp <= (Pa46*3.5)/5.5 ? "4x6" : "NG!"
      : maxComp <= Pa226 ? "(2) 2x6" : maxComp <= Pa46 ? "4x6" : maxComp <= Pa66 ? "6x6" : maxComp <= Pa68 ? "6x8" : "NG!";
  // HOLDOWNS
  const maxUplift = xMax(upHD_S, upHD_W);
  const isWood = seg.anchor === "Wood";
  let hd;
  if (maxUplift === 0) hd = "None";
  else { const found = HD_TABLE.find((x) => maxUplift < x.cap); hd = found ? (isWood ? `(2) ${found.name}` : found.name) : "NG!"; }
  const anchorFor = (variant) => {
    if (maxUplift === 0 || hd === "None") return "None";
    if (seg.anchor === "Concrete") {
      if (hd === "HDU2") return maxUplift < 4780 ? "SSTB16" : "5/8'' A.B.";
      if (hd === "HDU4") return maxUplift < 4780 ? "SSTB16" : "5/8'' A.B.";
      if (hd === "HDU5") return maxUplift < 5175 ? "SSTB24" : "5/8'' A.B.";
      if (hd === "HDU8") return maxUplift < 10100 ? "SSTB28" : "7/8'' A.B.";
      return "1'' A.B.";
    }
    if (seg.anchor === "Masonry") {
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
  const anchorEnd = seg.anchor === "Masonry" ? anchorFor("end") : anchorFor("interior");
  const embedFor = (anchorName, atEnd) => {
    if (anchorName === "None") return "None";
    if (["SSTB16","SSTB24","SSTB28"].includes(anchorName)) return "Simpson";
    if (seg.anchor === "Concrete") return Math.max(16, Math.floor(maxUplift / (atEnd ? 876 : 1752) + 5));
    if (seg.anchor === "Masonry") return Math.max(16, Math.floor(maxUplift / (atEnd ? 254 : 508) + 5));
    return "Threaded";
  };
  const embed = embedFor(anchorSel, false);
  const embedEnd = embedFor(anchorEnd, true);
  // STRAPS
  const maxStrap = xMax(upStrap_S, upStrap_W);
  const strapFor = (lims) => {
    if (maxUplift === 0) return "None";
    if (seg.anchor === "Concrete") { for (const [lim, name] of lims) if (maxStrap < lim) return name; return "None"; }
    if (seg.anchor === "Wood") {
      const woodLims = [[2010,"MST37"],[3105,"MST48"],[4800,"MST60"],[5660,"MSTC78"],[9235,"CMST12"]];
      for (const [lim, name] of woodLims) if (maxStrap < lim) return name; return "None";
    }
    return "None";
  };
  const altStrap = strapFor([[3195,"STHD8"],[3730,"STHD10"],[5785,"STHD14"]]);
  const strapCorner = strapFor([[2370,"STHD8"],[3730,"STHD10"],[5025,"STHD14"]]);
  const sugMax = xMax(sugS, sugW);
  const status = sugS === "FAILED!!!" || sugW === "FAILED!!!" ? "FAILED!!!" : seg.selType < sugMax ? "FAILED!!!" : "OK";
  // DEFLECTION
  const Epost = ["(2) 2x4","4x4","(2) 2x6","4x6"].includes(post) ? (sp ? 1400000 : 1600000) : (sp ? 1500000 : 1300000);
  const Apost = post === "(2) 2x4" ? 10.5 : post === "4x4" ? 12.25 : post === "(2) 2x6" ? 16.5 : post === "4x6" ? 19.25 : post === "6x6" ? 30.25 : 39.875;
  const Ga = SCHED[Math.max(0, Math.min(SCHED.length - 1, seg.selType - 1))].ga;  // marks 1–6; 4–6 carry the 2× combined Ga
  const defl = (v) => (8*(v/0.7)*Math.pow(h,3))/(Epost*Apost*L) + ((v/0.7)*h)/(1000*Ga) + (h/L)*0.125;
  const deflS = defl(vS);
  const deflW = defl(vW);
  // FOOTING
  const ftgW = seg.ftgWidth, ftgT = seg.ftgThick;
  const quad = (a, b, c) => { const disc = b*b - 4*a*c; if (disc < 0 || a === 0) return NaN; return (-b + Math.sqrt(disc)) / (2*a); };
  const a = (Math.min(0.6, B) * 150 * ftgW * ftgT) / 24;
  const P65 = (MotS + BwDL*L*(L/2 - seg.hdDist/12)) / (L - (1.5 + seg.hdDist)/12);
  const uS = numOr0(upHD_S);
  const LminS = quad(a, (P65-uS)/2, uS*(seg.hdDist/12 - L/2) + P65*(1.5/12 - L/2) - (Fs*ftgT)/12);
  const P70 = (MotW + CwDL*L*(L/2 - seg.hdDist/12)) / (L - (1.5 + seg.hdDist/12)/12);
  const uW = numOr0(upHD_W);
  const LminW = quad(a, (P70-uW)/2, uW*(seg.hdDist/12 - L/2) + P70*(1.5/12 - L/2) - (Fw*ftgT)/12);
  const reqFtgLen = xMax(L + 1, LminS, LminW);
  return {
    active:true, aspect, aspectNG, wdl,
    Fs, vS, factor, allowS, sugS, MotS, A, AwDL, compS, B, BwDL, upHD_S, upStrap_S,
    Fw, vW, sugW, MotW, compW, C:Cfac, CwDL, upHD_W, upStrap_W,
    maxComp, post, Pa:{Pa224,Pa44,Pa226,Pa46,Pa66,Pa68},
    maxUplift, hd, anchorSel, anchorEnd, embed, embedEnd,
    maxStrap, altStrap, strapCorner,
    status, deflS, deflW, LminS, LminW, reqFtgLen,
  };
}

// ---------- Design engine (verbatim search; per-line g) ----------
function baseDesignSeg(d) {
  return { height:d.height, roofTrib:d.roofTrib, floorTrib:d.floorTrib, hdDist:d.hdDist,
           thickness:d.thickness, anchor:d.anchor, selType:1, ftgWidth:d.ftgWidth, ftgThick:d.ftgThick };
}
function evaluateCandidate(Ls, totalL, g, d) {
  const seg = { ...baseDesignSeg(d), length: Ls };
  const r1 = calcSegment({ ...seg, selType: 1 }, g, totalL);
  if (!r1.active || r1.aspectNG) return null;
  if (!isNum(r1.sugS) || !isNum(r1.sugW)) return null;
  const type = Math.max(r1.sugS, r1.sugW);
  const r = calcSegment({ ...seg, selType: type }, g, totalL);
  if (r.post === "NG!" || r.hd === "NG!" || r.hd === "NG!!" || r.status !== "OK") return null;
  if (r.anchorSel === "NG!!") return null;
  return { type, r };
}
function generateDesign(g, d) {
  const snap = Math.max(0.25, d.snap || 0.5);
  const maxN = Math.max(1, Math.min(6, Math.floor(d.maxSegments)));
  // The "Max SW type" constraint caps the SINGLE-SIDED nailing the optimizer may use (1–3). Double-
  // sided marks (4–6) are NOT a user ceiling — they are an automatic LAST RESORT (below).
  const singleCap = Math.max(1, Math.min(3, Math.floor(d.maxType)));
  // One sweep over a contiguous mark band [Tlo,Thi]; minMark gates out lower marks so the double-sided
  // pass can't re-admit a single-sided solution the cap excluded. minMark=1 ⇒ inner gate is exactly the
  // original `ev.type<=T`, so the single-sided sweep is byte-identical to the prior optimizer.
  const sweep = (Tlo, Thi, minMark) => {
    const sols = [];
    for (let T = Tlo; T <= Thi; T++) {
      for (let N = 1; N <= maxN; N++) {
        const maxLs = Math.min(d.maxSegLen, d.lineLength / N);
        if (maxLs < d.minSegLen - 1e-9) continue;
        const start = Math.ceil(d.minSegLen / snap) * snap;
        for (let Ls = start; Ls <= maxLs + 1e-9; Ls = +(Ls + snap).toFixed(4)) {
          const ev = evaluateCandidate(Ls, N * Ls, g, d);
          if (ev && ev.type <= T && ev.type >= minMark) { sols.push({ T: ev.type, N, Ls, total: N * Ls, r: ev.r }); break; }
        }
      }
      if (d.objective === "nailing" && sols.some((s) => s.T <= T)) break;
    }
    return sols;
  };
  // LAST RESORT: only fall to double-sided (4–6) when NO single-sided (1–singleCap) solution exists at
  // all. The fallback accepts ONLY genuine double-sided requirements (mark ≥ 4) — a line that fails
  // single-sided merely because of the user's cap is NOT silently upgraded. For any line a single-sided
  // design can satisfy, this is byte-identical to the prior optimizer (the double sweep is never entered).
  let solutions = sweep(1, singleCap, 1);
  if (!solutions.length) solutions = sweep(4, 6, 4);
  if (!solutions.length) return null;
  solutions.sort((a, b) => d.objective === "nailing"
    ? a.T - b.T || a.total - b.total || a.N - b.N
    : a.total - b.total || a.N - b.N || a.T - b.T);
  const best = solutions[0];
  const gap = (d.lineLength - best.N * best.Ls) / (best.N + 1);
  const rnd = (x) => Math.round(x * 4) / 4;
  const segs = Array.from({ length: best.N }, (_, i) => ({ start: rnd(gap + i * (best.Ls + gap)), length: best.Ls }));
  return { segs, meta: { type: best.T, N: best.N, Ls: best.Ls, total: best.total } };
}

export {
  SCHEDULE, SCHEDULE_STR1, schedFor, NAIL_EDGE, CODES, HD_TABLE,
  isNum, xMax, numOr0, CP,
  calcSegment, baseDesignSeg, evaluateCandidate, generateDesign,
};
