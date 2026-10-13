import WebMu.Revised.TripodGraphData

namespace WebMu.Revised.TripodGraphs
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- All 95 original 33-point growth webs have the isolated positive tripod
at outputs 7--9. Removing it gives the corresponding 30-point growth web;
all boundary labels, vertex cyclic orders and orientations are retained.
Both rotation systems, including the fixed boundary rim, are planar. -/
theorem all_95_tripod_deletions :
    tripodData.size = 95 ∧ shortenedWords.size = 95 ∧ shortenedSteps.size = 95 ∧
    (List.range 95).all (fun i => tripodEntryValid i tripodData[i]!) = true := by native_decide

#print axioms all_95_tripod_deletions
end WebMu.Revised.TripodGraphs
