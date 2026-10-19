import MagHK.Ordering
import MagHK.CylindricalOrbitals
import Mathlib.MeasureTheory.Function.L2Space

/-!
A relative realization interface for the radial ordering argument.

The state space below is the actual complex L² space for r dr. The quadratic
forms are literal integrals of a weak derivative and the radial potentials.
`StandardRadialFacts` lists consequences of the general Friedrichs, weighted
Sobolev, ground-state transform, and closed-operator product theorems. These
facts are supplied as a parameter, never as new axioms. None of its fields
asserts an eigenvalue inequality, spectral ordering, or a manuscript lemma.

`orderingData` proves the adapter to `Ordering.RadialOrderingData`. Its
concrete inputs are coefficient regularity and endpoint bounds, positive
finite-energy differential solutions, and the two pointwise strict
inequalities. Providing the general library instance and packaging the
explicit manuscript functions remain separate obligations. In particular,
this module does not claim to construct mathlib's unbounded adjoint or
Friedrichs extension from first principles.
-/

noncomputable section
namespace MagHK.RadialRealization

open MeasureTheory Set Filter MagHK.Ordering
open scoped Topology ENNReal InnerProductSpace ContDiff

abbrev radialMeasure : Measure ℝ := MagHK.CylindricalOrbitals.radialMeasure
abbrev State := Lp ℂ 2 radialMeasure

def density (ψ : State) (r : ℝ) : ℝ := ‖ψ r‖ ^ 2

def mass (ψ : State) : ℝ := ∫ r, density ψ r ∂radialMeasure

def multiplier (w : ℝ → ℝ) (ψ : State) : ℝ :=
  ∫ r, w r * density ψ r ∂radialMeasure

theorem radialMeasure_positive : ∀ᵐ r ∂radialMeasure, 0 < r := by
  unfold radialMeasure MagHK.CylindricalOrbitals.radialMeasure
  rw [ae_withDensity_iff measurable_real_toNNReal.coe_nnreal_ennreal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact fun _ => hr

theorem density_integrable (ψ : State) : Integrable (density ψ) radialMeasure := by
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ)

theorem mass_eq_norm_sq (ψ : State) : mass ψ = ‖ψ‖ ^ 2 := by
  calc
    mass ψ = ∫ r, inner ℝ (ψ r) (ψ r) ∂radialMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (fun r => (real_inner_self_eq_norm_sq (ψ r)).symm)
    _ = inner ℝ ψ ψ := rfl
    _ = ‖ψ‖ ^ 2 := real_inner_self_eq_norm_sq ψ

theorem mass_pos (ψ : State) (hψ : ψ ≠ 0) : 0 < mass ψ := by
  rw [mass_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hψ)

theorem multiplier_pos (w : ℝ → ℝ) (ψ : State)
    (hw : ∀ r, 0 < r → 0 < w r) (hψ : ψ ≠ 0)
    (hi : Integrable (fun r => w r * density ψ r) radialMeasure) :
    0 < multiplier w ψ := by
  let wp : ℝ → ℝ := fun r => if 0 < r then w r else 1
  have heq : (fun r => wp r * density ψ r) =ᵐ[radialMeasure]
      (fun r => w r * density ψ r) := by
    filter_upwards [radialMeasure_positive] with r hr
    simp only [wp, if_pos hr]
  have h := strictly_positive_multiplier_integral radialMeasure wp (density ψ)
    (fun r => by dsimp [wp]; split_ifs with hr; exact hw r hr; norm_num)
    (fun r => sq_nonneg _) (density_integrable ψ) (hi.congr heq.symm) (mass_pos ψ hψ)
  change 0 < ∫ r, w r * density ψ r ∂radialMeasure
  rw [← integral_congr_ae heq]
  exact h

/-- Concrete, independently checkable hypotheses for the generic endpoint
and Friedrichs theorems. The partner coefficient after multiplication by
sqrt(r) is 3/(4r²) plus the displayed remainder. -/
structure CoefficientConditions (a v U : ℝ → ℝ) : Prop where
  a_smooth : ContDiff ℝ ∞ a
  v_smooth : ContDiff ℝ ∞ v
  U_smooth : ContDiff ℝ ∞ U
  a_zero : a 0 = 0
  U_zero : U 0 = 0
  riccati : ∀ r, 0 < r →
    v r = U r ^ 2 - deriv U r - U r / r - a r ^ 2
  scalar_tail_lower : ∃ R C : ℝ, 1 ≤ R ∧ ∀ r, R ≤ r → -C ≤ v r
  partner_origin_bound : ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 →
    |U r ^ 2 + deriv U r - U r / r| ≤ C
  partner_tail_lower : ∃ R C : ℝ, 1 ≤ R ∧ ∀ r, R ≤ r →
    -C ≤ 3 / (4 * r ^ 2) + U r ^ 2 + deriv U r - U r / r

/-- All the solution hypotheses are about actual functions, derivatives,
measures, and integrals. No operator eigenfunction assertion is included. -/
structure RegularSolution (a v : ℝ → ℝ) (m : ℤ) (E : ℝ)
    (u : ℝ → ℝ) (ψ : State) : Prop where
  smooth : ContDiffOn ℝ 2 u (Ioi 0)
  positive : ∀ r, 0 < r → 0 < u r
  bounded_origin : ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |u r| ≤ C
  finite_energy : Integrable
    (fun r => deriv u r ^ 2 + (((m : ℝ) / r + a r) ^ 2 + |v r|) * u r ^ 2)
    radialMeasure
  equation : ∀ r, 0 < r →
    radialExpression (m : ℝ) (a r) (v r) r (u r) (deriv u r) (deriv (deriv u) r) = E * u r
  represented : ∀ᵐ r ∂radialMeasure, ψ r = (u r : ℂ)
  positive_mass : 0 < ∫ r, u r ^ 2 ∂radialMeasure

theorem RegularSolution.nonzero {a v u : ℝ → ℝ} {m : ℤ} {E : ℝ} {ψ : State}
    (h : RegularSolution a v m E u ψ) : ψ ≠ 0 := by
  have hm : mass ψ = ∫ r, u r ^ 2 ∂radialMeasure := by
    apply integral_congr_ae
    filter_upwards [h.represented] with r hr
    simp only [density, hr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  intro hz
  have := h.positive_mass
  rw [← hm, mass_eq_norm_sq, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at this
  exact lt_irrefl 0 this

/-- The usual distributional derivative tested on real smooth functions
compactly supported inside the positive halfline. The integrals here use dr,
while the Hilbert-space and energy integrals use r dr. -/
def IsWeakDerivative (ψ : State) (dψ : ℝ → ℂ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    Function.support η ⊆ Ioi 0 →
      (∫ r : ℝ, ψ r * ((deriv η r : ℝ) : ℂ)) = -(∫ r : ℝ, dψ r * (η r : ℂ))

/-- Objects supplied by the general radial realization construction.
`weakDerivative` denotes the weak radial derivative on each form domain.
The `DomainOperator` type retains every operator domain explicitly. -/
structure RadialSystem where
  weakDerivative : State → ℝ → ℂ
  formDomain : ℤ → Submodule ℝ State
  L : ℤ → DomainOperator State
  D : DomainOperator State
  A : DomainOperator State

def quadratic (S : RadialSystem) (a v : ℝ → ℝ) (m : ℤ) (ψ : State) : ℝ :=
  ∫ r, ‖S.weakDerivative ψ r‖ ^ 2 +
    (((m : ℝ) / r + a r) ^ 2 + v r) * density ψ r ∂radialMeasure

def groundRemainder (S : RadialSystem) (u : ℝ → ℝ) (ψ : State) : ℝ :=
  ∫ r, ‖S.weakDerivative ψ r - (deriv u r / u r : ℂ) * ψ r‖ ^ 2 ∂radialMeasure

def angularDifference (a : ℝ → ℝ) (m : ℤ) (r : ℝ) : ℝ :=
  ((m : ℝ) / r + a r) ^ 2 - (-1 / r + a r) ^ 2

def partnerCorrection (a U : ℝ → ℝ) (r : ℝ) : ℝ := deriv U r + a r / r

def Eigen (S : RadialSystem) (m : ℤ) (E : ℝ) : Prop :=
  ∃ ψ : State, ∃ hψ : ψ ∈ (S.L m).domain,
    ψ ≠ 0 ∧ (S.L m).map ⟨ψ, hψ⟩ = E • ψ

/-- The exact generic analytic facts used by the adapter.

The realization field is the weighted Sobolev core theorem followed by
weak-to-operator realization. The ground-transform field is its integral
identity, not a lower-bound assumption. The comparison field is closure
of a nonnegative multiplication-form difference on a common smooth core.
The product fields follow from closure of the first-order form and the
limit-point theorem, using `CoefficientConditions` explicitly. The latter
conditions encode the critical 3/(4r²) endpoint and a tail lower bound.

A standard-library implementation must choose L as the Friedrichs
realizations, D as closure of d/dr+U, A=D*, and weakDerivative as the weak
derivative. This is a relative interface, not that implementation. -/
structure StandardRadialFacts (S : RadialSystem) (a v U : ℝ → ℝ) : Prop where
  radial_simplicity : ∀ (m : ℤ) (E : ℝ) (ψ φ : State) (hψ : ψ ∈ (S.L m).domain) (hφ : φ ∈ (S.L m).domain),
    ψ ≠ 0 → (S.L m).map ⟨ψ, hψ⟩ = E • ψ → (S.L m).map ⟨φ, hφ⟩ = E • φ →
      ∃ c : ℂ, φ = c • ψ
  weak_derivative : ∀ m ψ, ψ ∈ S.formDomain m → IsWeakDerivative ψ (S.weakDerivative ψ)
  form_integrable : ∀ m ψ, ψ ∈ S.formDomain m → Integrable
    (fun r => ‖S.weakDerivative ψ r‖ ^ 2 +
      (((m : ℝ) / r + a r) ^ 2 + v r) * density ψ r) radialMeasure
  D_action : ∀ ψ (hψ : ψ ∈ S.D.domain),
    ∀ᵐ r ∂radialMeasure, (S.D.map ⟨ψ, hψ⟩) r =
      S.weakDerivative ψ r + (U r : ℂ) * ψ r
  A_action : ∀ ψ (hψ : ψ ∈ S.A.domain),
    ∀ᵐ r ∂radialMeasure, (S.A.map ⟨ψ, hψ⟩) r =
      -S.weakDerivative ψ r - ψ r / (r : ℂ) + (U r : ℂ) * ψ r
  operator_to_form : ∀ m ψ, ψ ∈ (S.L m).domain → ψ ∈ S.formDomain m
  operator_energy : ∀ m ψ (hψ : ψ ∈ (S.L m).domain),
    quadratic S a v m ψ = inner ℝ ψ ((S.L m).map ⟨ψ, hψ⟩)
  regular_solution : CoefficientConditions a v U →
    ∀ m E u ψ, RegularSolution a v m E u ψ →
      ∃ hψ : ψ ∈ (S.L m).domain, (S.L m).map ⟨ψ, hψ⟩ = E • ψ
  ground_transform : ∀ E u ξ, RegularSolution a v (-1) E u ξ →
    ∀ ψ, ψ ∈ S.formDomain (-1) →
      quadratic S a v (-1) ψ = E * mass ψ + groundRemainder S u ψ
  positive_form_difference : ∀ m,
    (∀ r, 0 < r → 0 ≤ angularDifference a m r) →
    ∀ ψ, ψ ∈ S.formDomain m →
      ψ ∈ S.formDomain (-1) ∧
      Integrable (fun r => angularDifference a m r * density ψ r) radialMeasure ∧
      quadratic S a v m ψ = quadratic S a v (-1) ψ + multiplier (angularDifference a m) ψ
  zero_product : CoefficientConditions a v U →
    ∀ ψ (hψ : ψ ∈ (S.L 0).domain),
      ∃ hD : ψ ∈ S.D.domain, ∃ hA : S.D.map ⟨ψ, hD⟩ ∈ S.A.domain,
        S.A.map ⟨S.D.map ⟨ψ, hD⟩, hA⟩ = (S.L 0).map ⟨ψ, hψ⟩ ∧
        inner ℝ ψ ((S.L 0).map ⟨ψ, hψ⟩) = ‖S.D.map ⟨ψ, hD⟩‖ ^ 2
  partner_product : CoefficientConditions a v U →
    (∀ r, 0 < r → 0 ≤ partnerCorrection a U r) →
    ∀ φ (hA : φ ∈ S.A.domain) (hD : S.A.map ⟨φ, hA⟩ ∈ S.D.domain),
      φ ∈ S.formDomain (-1) ∧
      Integrable (fun r => partnerCorrection a U r * density φ r) radialMeasure ∧
      inner ℝ φ (S.D.map ⟨S.A.map ⟨φ, hA⟩, hD⟩) =
        quadratic S a v (-1) φ + 2 * multiplier (partnerCorrection a U) φ

/-- A single universal standard-theory premise, applicable independently of
the manuscript examples. The coefficient hypotheses are explicit, and the
returned realizations must satisfy all the actual integral and domain laws.
No instance of this library is asserted or postulated in this module. -/
def StandardRadialLibrary : Prop :=
  ∀ a v U : ℝ → ℝ, CoefficientConditions a v U →
    ∃ S : RadialSystem, StandardRadialFacts S a v U

private theorem eigen_energy (ψ : State) (E : ℝ) :
    inner ℝ ψ (E • ψ) = E * mass ψ := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, mass_eq_norm_sq]

private theorem ground_lower (S : RadialSystem) (a v U u : ℝ → ℝ) (lam : ℝ)
    (A : StandardRadialFacts S a v U) (ξ : State)
    (hu : RegularSolution a v (-1) lam u ξ) (ψ : State)
    (hψ : ψ ∈ S.formDomain (-1)) : lam * mass ψ ≤ quadratic S a v (-1) ψ := by
  rw [A.ground_transform lam u ξ hu ψ hψ]
  have hg : 0 ≤ groundRemainder S u ψ := integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- A proved adapter from concrete coefficient and positive-solution inputs.
Every eigenvalue comparison follows here from the generic identities above. -/
theorem orderingData (S : RadialSystem) (a v U u₀ u₁ : ℝ → ℝ) (lam : ℝ)
    (A : StandardRadialFacts S a v U) (hc : CoefficientConditions a v U)
    (ψ₀ ψ₁ : State) (hu₀ : RegularSolution a v 0 0 u₀ ψ₀)
    (hu₁ : RegularSolution a v (-1) lam u₁ ψ₁)
    (hlam : 0 < lam) (ha : ∀ r, 0 < r → 0 < r * a r ∧ r * a r < 1)
    (hW : ∀ r, 0 < r → 0 < partnerCorrection a U r) :
    RadialOrderingData (Eigen S) lam := by
  refine ⟨hlam, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hψ, heq⟩ := A.regular_solution hc 0 0 u₀ ψ₀ hu₀
    exact ⟨ψ₀, hψ, hu₀.nonzero, heq⟩
  · obtain ⟨hψ, heq⟩ := A.regular_solution hc (-1) lam u₁ ψ₁ hu₁
    exact ⟨ψ₁, hψ, hu₁.nonzero, heq⟩
  · intro E he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    obtain ⟨hD, hA, hprod, hnorm⟩ := A.zero_product hc ψ hψ
    let φ : State := S.D.map ⟨ψ, hD⟩
    have hE : E * mass ψ = mass φ := by
      rw [heq, eigen_energy] at hnorm
      exact hnorm.trans (mass_eq_norm_sq φ).symm
    refine ⟨mass ψ, mass φ, mass_pos ψ hne, by rw [mass_eq_norm_sq]; positivity, hE, ?_⟩
    intro hφmass
    have hφne : φ ≠ 0 := by
      intro hz
      rw [hz, mass_eq_norm_sq, norm_zero] at hφmass
      norm_num at hφmass
    have hprodE : S.A.map ⟨S.D.map ⟨ψ, hD⟩, hA⟩ = E • ψ := hprod.trans heq
    obtain ⟨hAD, htransfer⟩ := eigenvector_transfer S.D S.A ψ E hD hA hprodE
    obtain ⟨hform, hint, hp⟩ := A.partner_product hc (fun r hr => (hW r hr).le) φ hA hAD
    have hδ : 0 < multiplier (partnerCorrection a U) φ := multiplier_pos _ φ hW hφne hint
    refine ⟨quadratic S a v (-1) φ, multiplier (partnerCorrection a U) φ,
      ground_lower S a v U u₁ lam A ψ₁ hu₁ φ hform, hδ, ?_⟩
    rw [htransfer, eigen_energy] at hp
    exact hp
  · intro E he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    refine ⟨mass ψ, quadratic S a v (-1) ψ, mass_pos ψ hne,
      ground_lower S a v U u₁ lam A ψ₁ hu₁ ψ (A.operator_to_form (-1) ψ hψ), ?_⟩
    rw [A.operator_energy (-1) ψ hψ, heq, eigen_energy]
  · intro m E hm0 hm1 he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    have hdiff : ∀ r, 0 < r → 0 < angularDifference a m r := by
      intro r hr
      exact all_other_sector_difference_pos m (a r) r hr (ha r hr).1 (ha r hr).2 hm0 hm1
    obtain ⟨hform, hint, hq⟩ := A.positive_form_difference m
      (fun r hr => (hdiff r hr).le) ψ (A.operator_to_form m ψ hψ)
    refine ⟨mass ψ, quadratic S a v (-1) ψ, multiplier (angularDifference a m) ψ,
      mass_pos ψ hne, ground_lower S a v U u₁ lam A ψ₁ hu₁ ψ hform,
      multiplier_pos _ ψ hdiff hne hint, ?_⟩
    rw [A.operator_energy m ψ hψ, heq, eigen_energy] at hq
    exact hq

end MagHK.RadialRealization
