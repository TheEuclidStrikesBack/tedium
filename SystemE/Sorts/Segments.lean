import SystemE.Sorts.Points

/--
A segment is defined by two endpoints.
-/
inductive Segment
| endpoints (a b : Point)

-- TODO (logan) : should we define Segments as quotients over symmetry of endpoints?

namespace Segment

def ptA : Segment → Point := fun l => l.1
def ptB : Segment → Point := fun l => l.2

@[simp]
lemma ptA_endpoint_eq {A B : Point} : Segment.ptA (Segment.endpoints A B) = A := rfl

@[simp]
lemma ptB_endpoint_eq {A B : Point} : Segment.ptB (Segment.endpoints A B) = B := rfl

-- 2D Euclidean distance
noncomputable def length : Segment → ℝ
| endpoints a b => (a - b)

noncomputable instance : Coe Segment ℝ := ⟨length⟩

end Segment

open Lean PrettyPrinter

syntax "(" term "─" term ")": term

macro_rules
| `(($t:term ─ $s:term)) => `(Segment.endpoints $t $s)

@[app_unexpander Segment.endpoints]
def unexpand_endpoints : Unexpander
| `($_ $t $s) => `(($t ─ $s))
| _ => throw ()

/- Copy (and ovveride) the notation for Abs.abs, -/
macro:max (priority := high) atomic("|" noWs) a:term noWs "|"  : term => `(Segment.length $a)

@[app_unexpander Segment.length]
def unexpand_length : Lean.PrettyPrinter.Unexpander
| `($_ $i:ident) => `(|$i:ident|)
| `($_ ($t:term ─ $s:term)) => `(|($t:term─$s:term)|)
| _ => throw ()

namespace Segment

@[simp]
lemma coe_length__eq_iff {S : Segment} {x : ℝ} : ↑(S) = x ↔ |S| = x := Iff.rfl

@[irreducible]
lemma length_def {l : Segment} : |l| = l.ptA - l.ptB := by rfl

end Segment

@[aesop [norm]]
axiom segment_length_symm {a b : Point} : (a─b) = (b─a)

instance : LT Segment := ⟨fun l₁ l₂ => |l₁| < |l₂|⟩

@[simp]
theorem segment_lt_iff {l₁ l₂ : Segment} : l₁ < l₂ ↔ |l₁| < |l₂| := by unfold LT.lt;unfold instLTSegment; rfl
