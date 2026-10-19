import MagHK.MonopoleTrial
import MagHK.OperatorSpectrum
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual spherical-chart L² sections, transition functions, and the
antisymmetric two-particle space. The integer `q` is twice the magnetic charge.
The azimuth cut and polar axes are null sets for these Hilbert spaces. -/
noncomputable section
namespace MagHK.MonopoleRealization
open MeasureTheory Set
open MagHK.Monopole MagHK.MonopoleTrial
open scoped ComplexConjugate

abbrev Chart := ℝ × Angle
def chartMeasure : Measure Chart := radialVolume.prod sphereMeasure
instance : SFinite chartMeasure := by unfold chartMeasure; infer_instance
abbrev State := Lp ℂ 2 chartMeasure
def pairMeasure : Measure (Chart × Chart) := chartMeasure.prod chartMeasure
instance : SFinite pairMeasure := by unfold pairMeasure; infer_instance
abbrev PairState := Lp ℂ 2 pairMeasure

def swap : PairState →ₗᵢ[ℂ] PairState :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap
def fermionSubspace : Submodule ℂ PairState := (swap.toLinearMap + LinearMap.id).ker
abbrev FermionState := fermionSubspace
abbrev System := MagHK.Ordering.DomainOperator State
abbrev FermionSystem := MagHK.Ordering.DomainOperator FermionState

/-- North-to-south section transition for the convention −i∇+A. -/
def transition (q : ℤ) (φ : ℝ) : ℂ := Complex.exp (Complex.I * (q : ℝ) * φ)
def northCoefficient (q : ℤ) (μ : ℝ) : ℝ := (q : ℝ) / 2 * (1 - μ)
def southCoefficient (q : ℤ) (μ : ℝ) : ℝ := -(q : ℝ) / 2 * (1 + μ)

theorem transition_norm (q : ℤ) (φ : ℝ) : ‖transition q φ‖ = 1 := by
  simp [transition, Complex.norm_exp]

theorem connection_difference (q : ℤ) (μ : ℝ) :
    northCoefficient q μ - southCoefficient q μ = q := by
  unfold northCoefficient southCoefficient
  ring

theorem transition_periodic (q : ℤ) : Function.Periodic (transition q) (2 * Real.pi) := by
  intro φ
  unfold transition
  have he : Complex.I * ((q : ℝ) : ℂ) * ((φ + 2 * Real.pi : ℝ) : ℂ) =
      Complex.I * ((q : ℝ) : ℂ) * φ + (q : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

def southRepresentative (q : ℤ) (f : Chart → ℂ) (x : Chart) : ℂ :=
  transition q x.2.2 * f x

theorem southRepresentative_norm (q : ℤ) (f : Chart → ℂ) (x : Chart) :
    ‖southRepresentative q f x‖ = ‖f x‖ := by
  simp [southRepresentative, transition_norm]

/-- Permutation from particle grouping to the grouping used in the trial integral. -/
def regroup : (Chart × Chart) ≃ᵐ TrialCoordinates where
  toEquiv := Equiv.prodProdProdComm ℝ Angle ℝ Angle
  measurable_toFun := by
    change Measurable (fun p : Chart × Chart => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : TrialCoordinates => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    fun_prop

theorem regroup_measurePreserving : MeasurePreserving regroup pairMeasure trialMeasure := by
  have hmiddle : MeasurePreserving (fun x : Angle × (ℝ × Angle) => (x.2.1, (x.1, x.2.2)))
      (sphereMeasure.prod (radialVolume.prod sphereMeasure))
      (radialVolume.prod (sphereMeasure.prod sphereMeasure)) :=
    (measurePreserving_prodAssoc radialVolume sphereMeasure sphereMeasure).comp
      ((Measure.measurePreserving_swap.prod (MeasurePreserving.id sphereMeasure)).comp
        (MeasurePreserving.symm MeasurableEquiv.prodAssoc
          (measurePreserving_prodAssoc sphereMeasure radialVolume sphereMeasure)))
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc radialVolume radialVolume (sphereMeasure.prod sphereMeasure))).comp
      (((MeasurePreserving.id radialVolume).prod hmiddle).comp
        (measurePreserving_prodAssoc radialVolume sphereMeasure (radialVolume.prod sphereMeasure)))

def determinant (f g : Chart → ℂ) (p : Chart × Chart) : ℂ :=
  MagHK.Slater.slaterSlice (f p.1) (g p.1) f g p.2

def trialWave : Chart × Chart → ℂ := determinant orbitalPlus orbitalMinus

theorem trialWave_eq (p : Chart × Chart) : trialWave p = trial (regroup p) :=
  (trial_is_determinant p.1.1 p.2.1 p.1.2 p.2.2).symm

theorem trialWave_normalized : (∫ p, Complex.normSq (trialWave p) ∂pairMeasure) = 1 := by
  simp_rw [trialWave_eq]
  rw [regroup_measurePreserving.integral_comp' (fun x => Complex.normSq (trial x)), trial_normalized]

theorem trialWave_integrable_normSq : Integrable (fun p => Complex.normSq (trialWave p)) pairMeasure := by
  simpa only [trialWave_eq, Function.comp_def] using
    (regroup_measurePreserving.integrable_comp_of_integrable trial_integrable_normSq)

theorem trialWave_antisymmetric (x y : Chart) : trialWave (y, x) = -trialWave (x, y) := by
  unfold trialWave determinant MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  ring

private theorem radial_pairing (f g : Angle → ℂ) (x : Chart) :
    conj ((radialOrbital x.1 : ℂ) * f x.2) * ((radialOrbital x.1 : ℂ) * g x.2) =
      (radialOrbital x.1 ^ 2 : ℝ) * (conj (f x.2) * g x.2) := by
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

private theorem separated_integral (h : Angle → ℂ) :
    (∫ x : Chart, (radialOrbital x.1 ^ 2 : ℝ) * h x.2 ∂chartMeasure) =
      ∫ p, h p ∂sphereMeasure := by
  rw [chartMeasure, integral_prod_mul (fun r => ((radialOrbital r ^ 2 : ℝ) : ℂ)) h,
    integral_complex_ofReal, radialOrbital_normalized_radialVolume, Complex.ofReal_one, one_mul]

theorem orbital_pair_orthonormal : MagHK.Slater.OrthonormalPair chartMeasure orbitalPlus orbitalMinus := by
  have hr : Integrable (fun r => ((radialOrbital r ^ 2 : ℝ) : ℂ)) radialVolume :=
    radialOrbital_integrable_radialVolume.ofReal
  have ha := doublet_orthonormal
  constructor
  · simpa only [orbitalPlus, Complex.star_def, radial_pairing, chartMeasure] using hr.mul_prod ha.integrable_ff
  · simpa only [orbitalMinus, Complex.star_def, radial_pairing, chartMeasure] using hr.mul_prod ha.integrable_gg
  · simpa only [orbitalPlus, orbitalMinus, Complex.star_def, radial_pairing, chartMeasure] using hr.mul_prod ha.integrable_fg
  · simpa only [orbitalPlus, orbitalMinus, Complex.star_def, radial_pairing, chartMeasure] using hr.mul_prod ha.integrable_gf
  · simp only [orbitalPlus, Complex.star_def, radial_pairing]
    exact (separated_integral (fun p => conj (Yplus p) * Yplus p)).trans ha.norm_f
  · simp only [orbitalMinus, Complex.star_def, radial_pairing]
    exact (separated_integral (fun p => conj (Yminus p) * Yminus p)).trans ha.norm_g
  · simp only [orbitalPlus, orbitalMinus, Complex.star_def, radial_pairing]
    exact (separated_integral (fun p => conj (Yplus p) * Yminus p)).trans ha.orthogonal_fg
  · simp only [orbitalPlus, orbitalMinus, Complex.star_def, radial_pairing]
    exact (separated_integral (fun p => conj (Yminus p) * Yplus p)).trans ha.orthogonal_gf

def coulomb (p : Chart × Chart) : ℝ :=
  1 / pairDistance p.1.1 p.2.1 (p.1.2, p.2.2)

theorem coulomb_nonnegative (p : Chart × Chart) : 0 ≤ coulomb p := by
  unfold coulomb pairDistance
  positivity

theorem trial_coulomb_integral_transport :
    (∫ p, coulomb p * Complex.normSq (trialWave p) ∂pairMeasure) =
      ∫ x, Complex.normSq (trial x) / pairDistance x.1.1 x.1.2 x.2 ∂trialMeasure := by
  calc
    _ = ∫ p, Complex.normSq (trial (regroup p)) /
        pairDistance (regroup p).1.1 (regroup p).1.2 (regroup p).2 ∂pairMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by
        dsimp only
        rw [trialWave_eq]
        change (1 / pairDistance p.1.1 p.2.1 (p.1.2, p.2.2)) *
          Complex.normSq (trial (regroup p)) =
          Complex.normSq (trial (regroup p)) / pairDistance p.1.1 p.2.1 (p.1.2, p.2.2)
        ring)
    _ = _ := regroup_measurePreserving.integral_comp'
      (fun x => Complex.normSq (trial x) / pairDistance x.1.1 x.1.2 x.2)

end MagHK.MonopoleRealization
