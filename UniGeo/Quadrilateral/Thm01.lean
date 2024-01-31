import SystemE
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_1 : ∀ (Q R S T : Point) (QR ST RS QT QS : Line),
  formQuadrilateral Q R S T QR ST RS QT ∧
  distinctPointsOnLine Q S QS ∧
  ∠ Q:R:S = ∟ ∧
  ∠ Q:T:S = ∟ ∧
  ∠ Q:S:R = ∠ S:Q:T →
  |(S─T)| = |(Q─R)| :=
by
  euclid_intros
  euclid_assert (△ Q:S:T).congruent (△ S:Q:R)
  euclid_apply Triangle.congruent_if (△ Q:S:T) (△ S:Q:R)
  -- euclid_finish
  admit

end UniGeo.Quadrilateral
