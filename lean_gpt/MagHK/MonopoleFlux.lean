import MagHK.SpinGeometry
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Literal curvature, spherical flux and local gauge obstruction for the two
monopole signs. Smooth local gauge primitives are ruled out on every open
neighborhood, already in one chart. -/
noncomputable section
namespace MagHK.MonopoleFlux
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.SpinChart
open scoped ContDiff Topology

/-- The magnetic vector field in ordinary Euclidean space. -/
def field (q : ℤ) (x : Space) : Space := ((q : ℝ) / 2 / ‖x‖ ^ 3) • x

def flux (q : ℤ) (r : ℝ) : ℝ :=
  ∫ p, inner ℝ (field q (r • MagHK.MonopoleQuadrature.direction p))
      (MagHK.MonopoleQuadrature.direction p) * r ^ 2 ∂sphereMeasure

theorem flux_eq (q : ℤ) (r : ℝ) (hr : 0 < r) : flux q r = 2 * Real.pi * q := by
  have he : (fun p => inner ℝ (field q (r • MagHK.MonopoleQuadrature.direction p))
      (MagHK.MonopoleQuadrature.direction p) * r ^ 2) =ᵐ[sphereMeasure]
        fun _ => (q : ℝ) / 2 := by
    filter_upwards [angle_ae] with p hp
    have hn := MagHK.MonopoleQuadrature.direction_norm p hp
    have hnr : ‖r • MagHK.MonopoleQuadrature.direction p‖ = r := by
      rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    simp only [field, hnr, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
    field_simp
    <;> ring
  rw [flux, integral_congr_ae he, integral_const]
  rw [Measure.real, MagHK.MonopolePairLaw.sphereMeasure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi)]
  dsimp only [smul_eq_mul]
  ring

/-- The local curvature coefficient with the outward spherical orientation.
The area form is −dμ∧dφ in this chart. -/
def northCurvature (q : ℤ) (μ : ℝ) : ℝ := -deriv (northCoefficient q) μ

theorem northCurvature_eq (q : ℤ) (μ : ℝ) : northCurvature q μ = (q : ℝ) / 2 := by
  have hd := (((hasDerivAt_id μ).const_sub 1).const_mul ((q : ℝ) / 2)).deriv
  change deriv (northCoefficient q) μ = (q : ℝ) / 2 * (-1) at hd
  rw [northCurvature, hd]
  ring

/-- Local smooth gauge equivalence of the actual connection one-forms.
An ordinary smooth bundle gauge has such a real phase in a neighborhood
of each point. The basepoint is chosen away from both polar axes. -/
def LocallyGaugeEquivalent (q q' : ℤ) : Prop :=
  ∃ s : Set Angle, IsOpen s ∧ (0, 0) ∈ s ∧ ∃ χ : Angle → ℝ,
    ContDiffOn ℝ 2 χ s ∧ ∀ p ∈ s,
      fderiv ℝ χ p (1, 0) = 0 ∧
      fderiv ℝ χ p (0, 1) = northCoefficient q' p.1 - northCoefficient q p.1

theorem local_gauge_charge_eq (q q' : ℤ) (h : LocallyGaugeEquivalent q q') : q = q' := by
  rcases h with ⟨s, hs, hp, χ, hχ, hg⟩
  let p : Angle := (0, 0)
  have hc : ContDiffAt ℝ 2 χ p := (hχ p hp).contDiffAt (hs.mem_nhds hp)
  have hd : DifferentiableAt ℝ (fderiv ℝ χ) p :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₀ : (fun y => fderiv ℝ χ y (1, 0)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hp] with y hy
    exact (hg y hy).1
  have h₁ : (fun y => fderiv ℝ χ y (0, 1)) =ᶠ[𝓝 p]
      (fun y : Angle => northCoefficient q' y.1 - northCoefficient q y.1) := by
    filter_upwards [hs.mem_nhds hp] with y hy
    exact (hg y hy).2
  have hz := congrArg (fun T : Angle →L[ℝ] ℝ => T (0, 1)) h₀.fderiv_eq
  have hz' := congrArg (fun T : Angle →L[ℝ] ℝ => T (1, 0)) h₁.fderiv_eq
  have he : fderiv ℝ (fun y => fderiv ℝ χ y (0, 1)) p (1, 0) =
      fderiv ℝ (fun y => fderiv ℝ χ y (1, 0)) p (0, 1) := by
    rw [fderiv_clm_apply hd (differentiableAt_const (0, 1)),
      fderiv_clm_apply hd (differentiableAt_const (1, 0))]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using hc.isSymmSndFDerivAt (by norm_num) (1, 0) (0, 1)
  have hfst : HasFDerivAt (fun y : Angle => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hconst : HasFDerivAt (fun _ : Angle => (1 : ℝ)) (0 : Angle →L[ℝ] ℝ) p :=
    hasFDerivAt_const 1 p
  have hder := ((hconst.sub hfst).const_mul ((q' : ℝ) / 2)).sub
      ((hconst.sub hfst).const_mul ((q : ℝ) / 2))
  have hval := congrArg (fun T : Angle →L[ℝ] ℝ => T (1, 0)) hder.fderiv
  change fderiv ℝ (fun y : Angle => northCoefficient q' y.1 - northCoefficient q y.1) p (1, 0) = _ at hval
  simp at hval
  have hz0 : fderiv ℝ (fun y => fderiv ℝ χ y (1, 0)) p (0, 1) = 0 := by
    simpa using hz
  have hreal : (q : ℝ) = (q' : ℝ) := by linarith
  exact_mod_cast hreal

theorem opposite_charges_not_gauge : ¬ LocallyGaugeEquivalent 1 (-1) := by
  intro h
  have he := local_gauge_charge_eq 1 (-1) h
  norm_num at he

theorem opposite_fluxes (r : ℝ) (hr : 0 < r) : flux 1 r ≠ flux (-1) r := by
  rw [flux_eq 1 r hr, flux_eq (-1) r hr]
  norm_num
  exact ne_of_gt (by linarith [Real.pi_pos])

end MagHK.MonopoleFlux
