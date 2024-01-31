import SystemE.Sorts

@[irreducible]
def Point.onLine : Point → Line → Prop :=
fun p l => p ∈ l.toSet

@[simp]
abbrev distinctPointsOnLine : Point → Point → Line → Prop := fun P Q L => P.onLine L ∧ Q.onLine L ∧ P ≠ Q

namespace Point

@[irreducible]
def sameSide : Point → Point → Line → Prop :=
  fun ⟨x1,y1⟩ ⟨x2,y2⟩ ⟨a,b,c,_⟩  => (a*x1 + b*y1 + c)*(a*x2 + b*y2 + c) > 0

@[reducible, simp]
def opposingSides : Point → Point → Line → Prop :=
  fun a b l => ¬ a.onLine l ∧ ¬ b.onLine l ∧ ¬ sameSide a b l

def collinear (a b c : Point) : Prop := ∃ L : Line, a.onLine L ∧ b.onLine L ∧ c.onLine L

end Point

-- between x y z means y is between x and z
@[irreducible]
def between : Point → Point → Point → Prop :=
  fun a b c =>
    Point.collinear a b c ∧
    ((a.x < b.x ∧ b.x < c.x ∧ a.y < b.y ∧ b.y < c.y)
    ∨
    (a.x > b.x ∧ b.x > c.x ∧ a.y > b.y ∧ b.y > c.y))

namespace Point

@[irreducible]
def onCircle : Point → Circle → Prop :=
fun p c => p ∈ c.toSet

@[irreducible]
def insideCircle : Point → Circle → Prop :=
fun p c => p - c.centre < c.radius

abbrev outsideCircle : Point → Circle → Prop :=
fun p c => ¬ p.insideCircle c ∧ ¬ p.onCircle c

@[irreducible]
def isCentre : Point → Circle → Prop :=
fun p c => p = c.centre

end Point

namespace Line

@[irreducible]
def intersectsLine : Line → Line → Prop :=
fun l₁ l₂ => l₁ ≠ l₂ ∧ ∃ p : Point, p.onLine l₁ ∧ p.onLine l₂

@[irreducible]
def intersectsCircle : Line → Circle → Prop :=
fun l c =>  ∃ p : Point, p.onLine l ∧ p.onCircle c

end Line

namespace Circle

@[irreducible]
def intersectsCircle : Circle → Circle → Prop :=
fun c₁ c₂ => c₁ ≠ c₂ ∧ ∃ p : Point, p.onCircle c₁ ∧ p.onCircle c₂

end Circle

@[simp]
abbrev formTriangle (a b c : Point) (AB BC CA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧
  b.onLine BC ∧ c.onLine BC ∧ c.onLine CA ∧ a.onLine CA ∧
  AB ≠ BC ∧ BC ≠ CA ∧ CA ≠ AB

@[simp]
abbrev formRectilinearAngle (a b c : Point) (AB BC : Line) :=
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC

@[simp]
abbrev formParallelogram (a b c d : Point) (AB CD AC BD : Line) : Prop :=
    a.onLine AB ∧ b.onLine AB ∧ c.onLine CD ∧ d.onLine CD ∧ a.onLine AC ∧ c.onLine AC ∧ distinctPointsOnLine b d BD ∧
    (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ ¬(AC.intersectsLine BD)
