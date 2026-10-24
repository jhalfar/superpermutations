import N8Struct.Definitions

/-!
# Fact (3): the 27-walk

The closed walk of 27 loops with row lengths `266646664666466466646664666`, placed at the state
`012345`, is closed, costs Q = 16, and its 178 slices form a single closed trail.
Every theorem is checked by the kernel (`decide +kernel`); no `native_decide`.
-/

namespace N8Struct

open SuperpermutationUpperBound

/-- The row lengths of the 27-walk. -/
def vs27 : List Nat := [2,6,6,6,4,6,6,6,4,6,6,6,4,6,6,4,6,6,6,4,6,6,6,4,6,6,6]

/-- The 27-walk placed at the state `012345`. -/
def walk27 : List (Row Nat) := walkRows id6 vs27

theorem vs27_length : vs27.length = 27 := by decide

/-- The walk returns to `012345`, all row lengths are in 1..6, and it visits 27 different loops. -/
theorem walk27_closed : ClosedWalk id6 vs27 := by decide +kernel

/-- Consecutive rows are compatible in Pantone's sense at level 7 (tail = head), cyclically. -/
theorem walk27_pantone_compatible : CyclicallyCompatible walk27 := by
  unfold CyclicallyCompatible Row.Compatible
  decide +kernel

theorem walk27_Q : Q walk27 = 16 := by decide +kernel

/-- The tool's port rule (model.py `port_trails`): the port map is a permutation of the 5 strands
with one cycle, and no row has length 5, so the walk is one closed trail. -/
theorem walk27_port_perm : PortPerm vs27 := by decide +kernel
theorem walk27_portTrails : portTrails vs27 = 1 := by decide +kernel

theorem walk27_slices_length : (slices walk27).length = 178 := by decide +kernel

def trailOrder : List Nat := [0,13,18,23,28,37,42,47,52,57,66,71,76,81,90,95,100,109,114,119,124,129,138,143,148,153,162,167,172,177,4,11,16,21,26,31,40,45,50,55,64,69,74,79,84,86,87,85,88,93,98,103,112,117,122,127,136,141,146,151,156,158,159,157,160,165,170,175,2,6,7,8,9,5,12,17,22,27,32,34,35,33,36,41,46,51,56,65,70,75,80,89,94,99,104,106,107,105,108,113,118,123,128,137,142,147,152,161,166,171,176,3,10,15,20,25,30,39,44,49,54,63,68,73,78,83,92,97,102,111,116,121,126,135,140,145,150,155,164,169,174,1,14,19,24,29,38,43,48,53,58,60,61,59,62,67,72,77,82,91,96,101,110,115,120,125,130,132,133,131,134,139,144,149,154,163,168,173]

/-- The slices of the 27-walk in trail order (computed by gen.py; any order would be checked). -/
def walk27Trail : List (Row Nat) :=
  trailOrder.map (fun i => (slices walk27).getD i ⟨[], 0, 0⟩)

theorem walk27Trail_perm : walk27Trail.Perm (slices walk27) := by decide +kernel

theorem walk27Trail_closed : ClosedTrail walk27Trail := by
  unfold ClosedTrail CyclicallyCompatible Row.Compatible
  decide +kernel

theorem walk27Trail_heads_nodup : (walk27Trail.map Row.head).Nodup := by decide +kernel

/-- Fact (3), literal form: the 178 slices of the 27-walk are one closed trail. -/
theorem walk27_single_trail : SingleClosedTrail walk27 :=
  ⟨walk27Trail, walk27Trail_perm, walk27Trail_closed, walk27Trail_heads_nodup⟩

end N8Struct

#print axioms N8Struct.walk27_closed
#print axioms N8Struct.walk27_pantone_compatible
#print axioms N8Struct.walk27_Q
#print axioms N8Struct.walk27_port_perm
#print axioms N8Struct.walk27_portTrails
#print axioms N8Struct.walk27_single_trail
