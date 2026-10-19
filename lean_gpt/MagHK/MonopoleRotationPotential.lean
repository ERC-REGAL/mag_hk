import MagHK.MonopoleFormCovariance

/-! Rotation invariance of the literal Euclidean Coulomb multiplier. -/
noncomputable section
namespace MagHK.MonopoleCovariance
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.SpinChart
open MagHK.MonopoleTrial
set_option maxHeartbeats 1000000

theorem pairDistance_eq_point_norm (s t : ℝ) (p q : Angle)
    (hp : p.1 ∈ Icc (-1 : ℝ) 1) (hq : q.1 ∈ Icc (-1 : ℝ) 1) :
    pairDistance s t (p, q) = ‖point (s, p) - point (t, q)‖ := by
  rw [pairDistance_eq s t (p, q) hp hq, ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [norm_sub_sq_real]
  simp only [point, norm_smul, Real.norm_eq_abs,
    MagHK.MonopoleQuadrature.direction_norm p hp,
    MagHK.MonopoleQuadrature.direction_norm q hq, mul_one,
    sq_abs, real_inner_smul_left, real_inner_smul_right,
    ← MagHK.MonopolePairLaw.pairDot_eq_inner p q hp hq]
  ring

theorem coulomb_rotation_invariant (q : ℤ) (R : AngularMomentumAction q) :
    RotationInvariantPotential q R coulomb := by
  intro U
  have hm := (movedPair_measurePreserving q R U).quasiMeasurePreserving.ae pair_angle_ae
  filter_upwards [pair_angle_ae, hm] with p hp hm
  unfold coulomb
  rw [pairDistance_eq_point_norm _ _ _ _ hm.1 hm.2,
    pairDistance_eq_point_norm _ _ _ _ hp.1 hp.2]
  change 1 / ‖point (movedChart U p.1) - point (movedChart U p.2)‖ = _
  rw [moved_point q R U p.1 hp.1, moved_point q R U p.2 hp.2,
    ← map_sub, LinearIsometryEquiv.norm_map]

end MagHK.MonopoleCovariance
