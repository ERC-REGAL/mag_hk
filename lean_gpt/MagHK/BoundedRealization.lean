import MagHK.RadialRealization
import MagHK.PartnerAsymptotics
import MagHK.OrbitalDomains

/-!
The bounded radial construction instantiated in the relative operator
interface. All coefficient, endpoint, differential-solution and finite-energy
inputs are discharged for the actual manuscript functions. The only remaining
parameters are the universal standard radial library and the general spectral
assembly facts. The latter describe the planar direct sum and its discrete
spectrum below the already computed threshold 441/4.
-/

noncomputable section
namespace MagHK.BoundedRealization

open MeasureTheory Set
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.PotentialInfinity
open MagHK.SecondOrbital MagHK.PartnerAsymptotics MagHK.OrbitalDomains
open MagHK.RadialRealization MagHK.Ordering

/-- Every input to the endpoint/closed-factorization theorem is checked. -/
theorem bounded_coefficients (t : ℝ) (ht : 0 < t) :
    CoefficientConditions (profileA t) (regularProfileV t) (profileU t) := by
  refine ⟨(profileA_contDiff t ht.le).of_le le_top, (regularProfileV_contDiff t ht.le).of_le le_top,
    (profileU_contDiff t ht.le).of_le le_top, ?_, profileU_at_zero t, ?_, ?_, ?_, ?_⟩
  · rw [profileA_eq_mul_coefficient]
    simp
  · intro r hr
    rw [regularProfileV_eq t r (ne_of_gt hr)]
    rfl
  · obtain ⟨C, hC⟩ := regularProfileV_bounded t ht
    exact ⟨1, C, le_rfl, fun r hr => (abs_le.mp (hC r (by linarith))).1⟩
  · obtain ⟨C, hC⟩ := profilePartnerRemainder_bounded t ht
    refine ⟨C, fun r hr _ => ?_⟩
    simpa only [profilePartnerRemainder, profileUCoefficient_eq_div t r (ne_of_gt hr)]
      using hC r hr.le
  · obtain ⟨C, hC⟩ := profilePartner_lower_bound t ht
    refine ⟨1, C, le_rfl, fun r hr => ?_⟩
    have hr0 : 0 < r := by linarith
    rw [← profilePartnerCoefficient_eq t r (ne_of_gt hr0)]
    exact hC r hr0.le

private theorem real_memLp (u : ℝ → ℝ) (hu : Continuous u)
    (hi : Integrable (fun r => u r ^ 2) radialMeasure) :
    MemLp (fun r => (u r : ℂ)) 2 radialMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp hu).aestronglyMeasurable).mpr
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hi

theorem zero_memLp (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun r => (profileF t r : ℂ)) 2 radialMeasure :=
  real_memLp _ (profileF_continuous t ht)
    (MagHK.CylindricalOrbitals.radialZero_sq_integrable t ht)

theorem minus_memLp (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun r => (boundedProduct t r : ℂ)) 2 radialMeasure :=
  real_memLp _ (boundedProduct_contDiff t ht).continuous
    (boundedProduct_mass_integrable t ht)

def zeroState (t : ℝ) (ht : 0 ≤ t) : State :=
  (zero_memLp t ht).toLp (fun r => (profileF t r : ℂ))

def minusState (t : ℝ) (ht : 0 ≤ t) : State :=
  (minus_memLp t ht).toLp (fun r => (boundedProduct t r : ℂ))

theorem bounded_zero_solution (t : ℝ) (ht : 0 < t) :
    RegularSolution (profileA t) (regularProfileV t) 0 0
      (profileF t) (zeroState t ht.le) := by
  refine ⟨profileF_contDiffOn_two t ht.le, fun r _ => profileF_pos t r,
    profileF_bounded_near_zero t ht.le, ?_, ?_,
    (zero_memLp t ht.le).coeFn_toLp, profileF_mass_positive t ht.le⟩
  · simpa only [Int.cast_zero] using profileF_form_integrable t ht
  · intro r hr
    simpa only [radialExpression, Int.cast_zero, zero_div, zero_add, zero_mul,
      regularProfileV_eq t r (ne_of_gt hr)] using bounded_zero_eigen_equation t r ht hr

theorem bounded_minus_solution (t : ℝ) (ht : 0 < t) :
    RegularSolution (profileA t) (regularProfileV t) (-1) 20
      (boundedProduct t) (minusState t ht.le) := by
  refine ⟨boundedProduct_contDiffOn_two t ht.le, fun r hr => boundedProduct_positive t r hr,
    boundedProduct_bounded_near_zero t ht.le, ?_, ?_,
    (minus_memLp t ht.le).coeFn_toLp, boundedProduct_mass_positive t ht.le⟩
  · simpa only [Int.cast_neg, Int.cast_one] using boundedProduct_form_integrable t ht
  · intro r hr
    simpa only [radialExpression, Int.cast_neg, Int.cast_one,
      regularProfileV_eq t r (ne_of_gt hr)] using bounded_eigen_equation t r ht hr

/-- Concrete radial ordering, conditional only on general realization facts. -/
theorem bounded_ordering (t : ℝ) (ht : 0 < t) (S : RadialSystem)
    (A : StandardRadialFacts S (profileA t) (regularProfileV t) (profileU t)) :
    RadialOrderingData (Eigen S) 20 := by
  apply orderingData S (profileA t) (regularProfileV t) (profileU t)
    (profileF t) (boundedProduct t) 20 A (bounded_coefficients t ht)
    (zeroState t ht.le) (minusState t ht.le)
    (bounded_zero_solution t ht) (bounded_minus_solution t ht) (by norm_num)
  · intro r hr
    exact profileA_bounds t r ht hr
  · intro r hr
    exact positive_margin_positive t r ht hr

/-- The literal one-dimensional complex radial eigenline property. -/
def SimpleRadialEigenline (S : RadialSystem) (m : ℤ) (E : ℝ) : Prop :=
  ∃ ψ : State, ∃ hψ : ψ ∈ (S.L m).domain, ψ ≠ 0 ∧
    (S.L m).map ⟨ψ, hψ⟩ = E • ψ ∧
    ∀ φ (hφ : φ ∈ (S.L m).domain), (S.L m).map ⟨φ, hφ⟩ = E • φ →
      ∃ c : ℂ, φ = c • ψ

theorem simple_radial_eigenline (S : RadialSystem) (a v U : ℝ → ℝ)
    (A : StandardRadialFacts S a v U) (m : ℤ) (E : ℝ) (he : Eigen S m E) :
    SimpleRadialEigenline S m E := by
  obtain ⟨ψ, hψ, hne, hE⟩ := he
  exact ⟨ψ, hψ, hne, hE, fun φ hφ hφE => A.radial_simplicity m E ψ φ hψ hφ hne hE hφE⟩

/-- General direct-sum and below-essential-spectrum facts. The multiplicity
field is a dimension consequence at every energy and sector, using the
actual radial eigenline property. It does not assume simplicity at 0 or 20.
A planar realization must identify `spectrum` and `multiplicity` with its
actual spectrum and complex eigenspace dimensions. -/
structure PlanarSpectralFacts (S : RadialSystem) (spectrum : Set ℝ)
    (multiplicity : ℝ → ℕ) (threshold : ℝ) : Prop where
  discrete : DiscreteSpectralAssembly (Eigen S) spectrum threshold
  dimension_of_single_eigenline : ∀ E m,
    (∀ n, Eigen S n E → n = m) → SimpleRadialEigenline S m E → multiplicity E = 1

/-- The two concrete planar levels, multiplicities, and a strict gap. -/
theorem bounded_planar_levels (t : ℝ) (ht : 0 < t) (S : RadialSystem)
    (A : StandardRadialFacts S (profileA t) (regularProfileV t) (profileU t))
    (spectrum : Set ℝ) (multiplicity : ℝ → ℕ)
    (hs : PlanarSpectralFacts S spectrum multiplicity (441 / 4)) :
    (∀ E, E ∈ spectrum ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
      multiplicity 0 = 1 ∧ multiplicity 20 = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ E, 20 < E → E < 20 + ε → E ∉ spectrum := by
  have ho := bounded_ordering t ht S A
  refine ⟨planar_spectrum_below_second ho hs.discrete (by norm_num), ?_, ?_,
    planar_strict_gap ho hs.discrete (by norm_num)⟩
  · exact hs.dimension_of_single_eigenline 0 0
      (fun n hn => unique_sector_at_zero ho hn)
      (simple_radial_eigenline S _ _ _ A 0 0 ho.zero_state)
  · exact hs.dimension_of_single_eigenline 20 (-1)
      (fun n hn => unique_sector_at_lambda ho hn)
      (simple_radial_eigenline S _ _ _ A (-1) 20 ho.minus_one_state)

/-- A universal standard radial library suffices for an actual realization
of every positive parameter. No operator-domain or ordering assertion about
the manuscript profiles is a premise. -/
theorem bounded_realization (library : StandardRadialLibrary) (t : ℝ) (ht : 0 < t) :
    ∃ S : RadialSystem,
      StandardRadialFacts S (profileA t) (regularProfileV t) (profileU t) ∧
      RadialOrderingData (Eigen S) 20 ∧
      ∀ spectrum multiplicity, PlanarSpectralFacts S spectrum multiplicity (441 / 4) →
        (∀ E, E ∈ spectrum ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
        multiplicity 0 = 1 ∧ multiplicity 20 = 1 ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ E, 20 < E → E < 20 + ε → E ∉ spectrum := by
  obtain ⟨S, A⟩ := library (profileA t) (regularProfileV t) (profileU t) (bounded_coefficients t ht)
  exact ⟨S, A, bounded_ordering t ht S A, fun spectrum multiplicity hs =>
    bounded_planar_levels t ht S A spectrum multiplicity hs⟩

/-- The spectral realization can be chosen at the actual equal-norm
parameter obtained from the proved improper-integral limits and IVT. -/
theorem exists_balanced_bounded_realization (library : StandardRadialLibrary) :
    ∃ t : ℝ, 0 < t ∧ radialNormF t = radialNormG t ∧ 0 < radialNormF t ∧
      ∃ S : RadialSystem,
        StandardRadialFacts S (profileA t) (regularProfileV t) (profileU t) ∧
        RadialOrderingData (Eigen S) 20 := by
  obtain ⟨t, ht, hnorm, hpos⟩ := exists_bounded_parameter
  obtain ⟨S, hS, ho, _⟩ := bounded_realization library t ht
  exact ⟨t, ht, hnorm, hpos, S, hS, ho⟩

end MagHK.BoundedRealization
