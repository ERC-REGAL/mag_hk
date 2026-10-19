import MagHK.MonopolePairLaw
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Rotation equivariance forces an actual vector field on Euclidean three-space to be radial. -/
noncomputable section
namespace MagHK.MonopoleRadiality
open MeasureTheory Set
open MagHK.MonopoleQuadrature MagHK.MonopolePairLaw

abbrev Proper (R : Space ≃ₗᵢ[ℝ] Space) : Prop := LinearMap.det R.toLinearMap = 1

theorem space_finrank : Module.finrank ℝ Space = 3 := by
  calc
    _ = Module.finrank ℝ (ℝ × ℂ) := (WithLp.linearEquiv 2 ℝ (ℝ × ℂ)).finrank_eq
    _ = 3 := by rw [Module.finrank_prod, Module.finrank_self, Complex.finrank_real_complex]

theorem halfTurn_proper (x : Space) (hx : x ≠ 0) : Proper (Submodule.reflection (ℝ ∙ x)) := by
  letI : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨space_finrank⟩
  rw [Proper, Submodule.det_reflection,
    Submodule.finrank_orthogonal_span_singleton (n := 2) hx]
  norm_num

theorem equivariant_mem_span (j : Space → Space)
    (hj : ∀ R : Space ≃ₗᵢ[ℝ] Space, Proper R → ∀ x, x ≠ 0 → j (R x) = R (j x))
    (x : Space) (hx : x ≠ 0) : j x ∈ ℝ ∙ x := by
  let R := Submodule.reflection (ℝ ∙ x)
  have hRx : R x = x := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self x)
  apply (Submodule.reflection_eq_self_iff (K := ℝ ∙ x) (j x)).mp
  exact (hj R (halfTurn_proper x hx) x hx).symm.trans (congrArg j hRx)

def eastPole : Space := WithLp.toLp 2 (0, 1)

theorem eastPole_nonzero : eastPole ≠ 0 := by
  intro he
  have h := congrArg (fun x : Space => (WithLp.ofLp x).2) he
  simpa [eastPole] using h

theorem eastPole_northPole_inner : inner ℝ eastPole northPole = 0 := by
  simp [eastPole, northPole, WithLp.prod_inner_apply]

/-- A concrete proper half-turn carries any nonzero point to the north point of the same radius. -/
theorem proper_to_north (x : Space) (hx : x ≠ 0) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, Proper R ∧ R x = ‖x‖ • northPole := by
  let y : Space := ‖x‖ • northPole
  have hy : ‖y‖ = ‖x‖ := by simp [y, norm_smul, northPole_norm]
  by_cases hsum : x + y = 0
  · refine ⟨Submodule.reflection (ℝ ∙ eastPole), halfTurn_proper eastPole eastPole_nonzero, ?_⟩
    have hxneg : x = -y := eq_neg_of_add_eq_zero_left hsum
    have horth : x ∈ (ℝ ∙ eastPole)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hxneg, inner_neg_left]
      simp [y, eastPole, northPole, WithLp.prod_inner_apply]
    calc
      _ = -x := Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg horth
      _ = y := by rw [hxneg, neg_neg]
  · refine ⟨Submodule.reflection (ℝ ∙ (x + y)), halfTurn_proper _ hsum, ?_⟩
    have hnorm : ‖x‖ = ‖-y‖ := by rw [norm_neg, hy]
    have h := Submodule.reflection_sub hnorm
    simp only [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
    exact neg_injective h

def radialCoefficient (j : Space → Space) (r : ℝ) : ℝ :=
  inner ℝ northPole (j (r • northPole))

theorem equivariant_radial (j : Space → Space)
    (hj : ∀ R : Space ≃ₗᵢ[ℝ] Space, Proper R → ∀ x, x ≠ 0 → j (R x) = R (j x))
    (x : Space) (hx : x ≠ 0) :
    j x = radialCoefficient j ‖x‖ • MagHK.MonopoleSphere.normalize x := by
  obtain ⟨R, hR, hRx⟩ := proper_to_north x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyne : ‖x‖ • northPole ≠ 0 := by
    rw [← hRx]
    exact R.map_ne_zero_iff.mpr hx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
    (equivariant_mem_span j hj (‖x‖ • northPole) hyne)
  have hjnorth : j (‖x‖ • northPole) = radialCoefficient j ‖x‖ • northPole := by
    have hself : inner ℝ northPole northPole = 1 := by rw [real_inner_self_eq_norm_sq, northPole_norm]; norm_num
    rw [← hb]
    simp only [radialCoefficient, ← hb, real_inner_smul_right, hself, mul_one, smul_smul]
  apply R.injective
  rw [← hj R hR x hx, hRx, hjnorth, map_smul,
    ← MagHK.MonopoleSphere.normalize_isometry R x, hRx]
  simp only [MagHK.MonopoleSphere.normalize, norm_smul, northPole_norm, mul_one,
    norm_norm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end MagHK.MonopoleRadiality
