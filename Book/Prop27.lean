import SystemE
import Book.Prop16


namespace Elements.Book1

theorem proposition_27 : ∀ (a b c d e f : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a e b) ∧ (between c f d) ∧ (b.sameSide d EF) ∧ ∠ a:e:f  = (∠ e:f:d) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  by_contra
  euclid_apply (intersection_lines AB CD) as g
  by_cases (g.sameSide b EF)
  . euclid_apply (proposition_16 f g e a CD AB EF)
    euclid_finish
  . -- Omitted by Euclid.
    euclid_apply (proposition_16 e g f d AB CD EF)
    euclid_finish

theorem proposition_27' : ∀ (a d e f : Point) (AB CD EF : Line),
  distinctPointsOnLine a e AB ∧ distinctPointsOnLine f d CD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ ∠ a:e:f = (∠ e:f:d) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  euclid_apply (extend_point AB a e) as b
  euclid_apply (extend_point CD d f) as c
  euclid_apply (proposition_27 a b c d e f AB CD EF)
  euclid_finish

end Elements.Book1
