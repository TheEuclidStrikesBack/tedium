
namespace SystemE.Tactics.Translation

inductive ESort
| Point
| Line
| Segment
| Circle
| Angle
| Area
deriving Inhabited

inductive ERelation
| OnL (point line : String)
| OnC (point circle : String)
| Centre (point circle : String)
| InC (point circle : String)
| SameSide (p₁ p₂ line : String)
| Between (p₁ p₂ p₃ : String)
| IntersectsLL (l₁ l₂ : String)
| IntersectsLC (l c : String)
| IntersectsCC (c₁ c₂ : String)

inductive EFun
| SegLen (endA endB : String)
| Deg (angle : String)


namespace ESort

def toString : ESort → String
| Point => "Point"
| Line => "Line"
| Segment => "Segment"
| Circle => "Circle"
| Angle => "Angle"
| Area => "Area"

instance : ToString ESort := ⟨toString⟩

def asConstDecl : String × ESort → String
| ⟨x, s⟩ => s!"(declare-const {x} {s})"

instance : ToString (String × ESort) := ⟨asConstDecl⟩

end ESort

namespace ERelation

def toString : ERelation → String
| OnL p l => s!"(OnL {p} {l})"
| OnC p C => s!"(OnC {p} {C})"
| Centre p C => s!"(Centre {p} {C})"
| InC p C => s!"(Inside {p} {C})"
| SameSide p₁ p₂ l => s!"(SameSide {p₁} {p₂} {l})"
| Between  p₁ p₂ p₃ => s!"(Between {p₁} {p₂} {p₃})"
| IntersectsLL l₁ l₂ => s!"(IntersectsLL {l₁} {l₂})"
| IntersectsLC l c => s!"(IntersectsLC {l} {c})"
| IntersectsCC c₁ c₂ => s!"(IntersectsCC {c₁} {c₂})"


instance : ToString ERelation := ⟨toString⟩

def asAssertion : ERelation → String := fun r => s!"(assert {r})"

end ERelation

abbrev EConst := String × ESort

inductive EAssertion
| erel (r : ERelation)
| eq (a b : String)
| lt (a b : String)
| lte (a b : String)
| gt (a b : String)
| gte (a b : String)
| neg (x : EAssertion)
| ex (x τ : String) (p : EAssertion)
| or (a b : EAssertion)
| and (a b : EAssertion)

instance : Inhabited EAssertion := ⟨EAssertion.eq "false" "true"⟩

def EAssertionToString : EAssertion → String
| EAssertion.erel r => s!"{r}"
| EAssertion.and a b => s!"(and {EAssertionToString a} {EAssertionToString b})"
| EAssertion.eq a b => s!"(= {a} {b})"
| EAssertion.lt a b => s!"(< {a} {b})"
| EAssertion.lte a b => s!"(<= {a} {b})"
| EAssertion.gt a b => s!"(> {a} {b})"
| EAssertion.gte a b => s!"(>= {a} {b})"
| EAssertion.neg x => s!"(not {EAssertionToString x})"
| EAssertion.ex x τ p => s!"(exists ({x} {τ}) {EAssertionToString p})"
| EAssertion.or a b => s!"(or {EAssertionToString a} {EAssertionToString b})"

instance : ToString EAssertion := ⟨EAssertionToString⟩

end SystemE.Tactics.Translation
