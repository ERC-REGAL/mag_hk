import MagHK.MonopoleGround
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Explicit endpoint and domain statements for the monopole appendix.
The external radial theorem is uniform in every nonnegative centrifugal
coefficient. The angular separation theorem is uniform in integer charge.
In particular the minimal operator core below uses regular angular harmonics
and compact radial factors. The polar-axis cutoff used by the earlier form
core must not be substituted for this operator core.
-/
noncomputable section
namespace MagHK.MonopoleEndpointDomains
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleTrial
open scoped ContDiff Topology ComplexConjugate BigOperators
set_option maxHeartbeats 1000000

abbrev radialMeasure : Measure ℝ := volume.restrict (Ioi 0)
abbrev RadialState := Lp ℂ 2 radialMeasure
abbrev RadialSystem := MagHK.Ordering.DomainOperator RadialState

def expression (c : ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  -deriv (deriv u) r + (c / r ^ 2 + r ^ 2 : ℝ) * u r

def RadialCore (u : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ioi 0

def radialForm (c : ℝ) (u v : ℝ → ℂ) : ℂ :=
  ∫ r, conj (deriv u r) * deriv v r + (c / r ^ 2 + r ^ 2 : ℝ) * conj (u r) * v r
    ∂radialMeasure

def LocallyAC (u : ℝ → ℂ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → AbsolutelyContinuousOnInterval u a b

def MaximalDomain (c : ℝ) (u : ℝ → ℂ) : Prop :=
  LocallyAC u ∧ LocallyAC (deriv u) ∧ MemLp u 2 radialMeasure ∧
    MemLp (expression c u) 2 radialMeasure

def boundary (ell : ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r ^ (ell + 1) : ℝ) * deriv u r - ((ell + 1) * r ^ ell : ℝ) * u r

def FriedrichsBoundary (ell : ℝ) (u : ℝ → ℂ) : Prop :=
  Tendsto (boundary ell u) (𝓝[>] 0) (𝓝 0)

def MinimalGraph {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (core : (X → ℂ) → Prop) (D : (X → ℂ) → X → ℂ)
    (ψ η : Lp ℂ 2 μ) : Prop :=
  ∃ f : ℕ → X → ℂ, ∃ u v : ℕ → Lp ℂ 2 μ,
    (∀ n, core (f n)) ∧ (∀ n, ∀ᵐ x ∂μ, u n x = f n x) ∧
    (∀ n, ∀ᵐ x ∂μ, v n x = D (f n) x) ∧
    Tendsto u atTop (𝓝 ψ) ∧ Tendsto v atTop (𝓝 η)

def adjointKernel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : MagHK.Ordering.DomainOperator H) (z : ℂ) : Submodule ℂ H :=
  Submodule.span ℂ {ψ | ∀ η (hη : η ∈ T.domain),
    inner ℂ (T.map ⟨η, hη⟩) ψ = inner ℂ η (z • ψ)}

def deficiency {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : MagHK.Ordering.DomainOperator H) (positive : Bool) : ℕ :=
  Module.finrank ℂ (adjointKernel T (if positive then Complex.I else -Complex.I))

/-- Square-integrable local solution space on an actual radial interval. -/
def localSolutionSpace (s : Set ℝ) (c : ℝ) (z : ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict s)) :=
  Submodule.span ℂ {ψ | ∃ u : ℝ → ℂ,
    (∀ᵐ r ∂volume.restrict s, ψ r = u r) ∧ ContDiffOn ℝ 2 u s ∧
      ∀ r ∈ s, expression c u r = z * u r}

/-- The standard generalized Laguerre polynomial, written as its finite sum. -/
def laguerre (n : ℕ) (α x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m / (Nat.factorial m : ℝ) *
    ((∏ j ∈ Finset.range (n - m), (α + m + 1 + j)) /
      (Nat.factorial (n - m) : ℝ)) * x ^ m

def oscillatorWave (ell : ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  (Real.sqrt (2 * Nat.factorial n / Real.Gamma (n + ell + 3 / 2)) *
    r ^ (ell + 1) * Real.exp (-r ^ 2 / 2) * laguerre n (ell + 1 / 2) (r ^ 2) : ℝ)

theorem laguerre_zero (α x : ℝ) : laguerre 0 α x = 1 := by simp [laguerre]

structure RadialFacts (ell : ℝ) (F M : RadialSystem) where
  selfadjoint : OperatorModel.SelfAdjoint F
  compact : OperatorModel.CompactResolvent F
  friedrichs : ∀ ψ η, (∃ h : ψ ∈ F.domain, F.map ⟨ψ, h⟩ = η) ↔
    FriedrichsGraph radialMeasure RadialCore (radialForm (ell * (ell + 1))) ψ η
  minimal_graph : ∀ ψ η, (∃ h : ψ ∈ M.domain, M.map ⟨ψ, h⟩ = η) ↔
    MinimalGraph radialMeasure RadialCore (expression (ell * (ell + 1))) ψ η
  domain_characterization : ∀ ψ,
    ψ ∈ F.domain ↔ ∃ u : ℝ → ℂ, (∀ᵐ r ∂radialMeasure, ψ r = u r) ∧
      MaximalDomain (ell * (ell + 1)) u ∧ (ell < 1 / 2 → FriedrichsBoundary ell u)
  action : ∀ ψ (h : ψ ∈ F.domain) u,
    (∀ᵐ r ∂radialMeasure, ψ r = u r) → MaximalDomain (ell * (ell + 1)) u →
    ∀ᵐ r ∂radialMeasure, F.map ⟨ψ, h⟩ r = expression (ell * (ell + 1)) u r
  deficiency_indices : ∀ positive, deficiency M positive = if ell < 1 / 2 then 1 else 0
  origin_solution_dimension : ∀ z : ℂ,
    Module.finrank ℂ (localSolutionSpace (Ioo 0 1) (ell * (ell + 1)) z) =
      if ell < 1 / 2 then 2 else 1
  infinity_solution_dimension : ∀ z : ℂ,
    Module.finrank ℂ (localSolutionSpace (Ioi 1) (ell * (ell + 1)) z) = 1
  regular_eigenfunction : ∀ E ψ, OperatorModel.Eigen F E ψ →
    ∃ u : ℝ → ℂ, (∀ᵐ r ∂radialMeasure, ψ r = u r) ∧ ContDiffOn ℝ 2 u (Ioi 0) ∧
      (∀ r, 0 < r → expression (ell * (ell + 1)) u r = (E : ℂ) * u r) ∧
      ∃ C : ℂ, C ≠ 0 ∧
        Tendsto (fun r => u r / (r ^ (ell + 1) : ℝ)) (𝓝[>] 0) (𝓝 C)
  basis : ℕ → RadialState
  basis_represented : ∀ n, ∀ᵐ r ∂radialMeasure, basis n r = oscillatorWave ell n r
  basis_orthonormal : Orthonormal ℂ basis
  basis_complete : Dense (Submodule.span ℂ (range basis) : Set RadialState)
  basis_eigen : ∀ n : ℕ, OperatorModel.Eigen F (4 * n + 2 * ell + 3) (basis n)
  basis_equation : ∀ (n : ℕ) r, 0 < r → expression (ell * (ell + 1)) (oscillatorWave ell n) r =
    ((4 * n + 2 * ell + 3 : ℝ) : ℂ) * oscillatorWave ell n r

/-- General singular-oscillator endpoint classification, principal Friedrichs
boundary condition and Laguerre spectral resolution, for every ell ≥ 0.
These are standard Sturm–Liouville and oscillator facts. The particular
monopole coefficients, angular multiplicities and deficiency count are not
assumed here. -/
def StandardSingularOscillatorLibrary : Prop :=
  ∀ ell : ℝ, 0 ≤ ell → ∃ F M : RadialSystem, Nonempty (RadialFacts ell F M)

def angularCoefficient (q : ℤ) (k : ℕ) : ℝ :=
  ((k : ℝ) + q.natAbs / 2) * ((k : ℝ) + q.natAbs / 2 + 1) - ((q : ℝ) / 2) ^ 2

def radialIndex (q : ℤ) (k : ℕ) : ℝ :=
  (Real.sqrt (1 + 4 * angularCoefficient q k) - 1) / 2

theorem coefficient_opposite (q : ℤ) (k : ℕ) : angularCoefficient (-q) k = angularCoefficient q k := by
  simp [angularCoefficient]
  ring

theorem index_opposite (q : ℤ) (k : ℕ) : radialIndex (-q) k = radialIndex q k := by
  simp only [radialIndex, coefficient_opposite]

theorem coefficient_one (k : ℕ) : angularCoefficient 1 k = (k : ℝ) ^ 2 + 2 * k + 1 / 2 := by
  norm_num [angularCoefficient]
  ring

theorem coefficient_one_nonneg (k : ℕ) : 0 ≤ angularCoefficient 1 k := by
  rw [coefficient_one]
  positivity

theorem index_quadratic (q : ℤ) (k : ℕ) (hc : 0 ≤ angularCoefficient q k) :
    radialIndex q k * (radialIndex q k + 1) = angularCoefficient q k := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * angularCoefficient q k)
  unfold radialIndex
  nlinarith

theorem index_nonneg (q : ℤ) (k : ℕ) (hc : 0 ≤ angularCoefficient q k) : 0 ≤ radialIndex q k := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * angularCoefficient q k)
  have hn := Real.sqrt_nonneg (1 + 4 * angularCoefficient q k)
  unfold radialIndex
  nlinarith

theorem index_one_zero : radialIndex 1 0 = MagHK.Monopole.ell := by
  norm_num [radialIndex, coefficient_one, MagHK.Monopole.ell]

theorem index_one_limit_circle (k : ℕ) : radialIndex 1 k < 1 / 2 ↔ k = 0 := by
  constructor
  · intro h
    have hq := index_quadratic 1 k (coefficient_one_nonneg k)
    have hn := index_nonneg 1 k (coefficient_one_nonneg k)
    rw [coefficient_one] at hq
    by_contra hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  · rintro rfl
    rw [index_one_zero]
    exact MagHK.Monopole.lowest_sector_limit_circle.2

theorem monopole_radial_domains (library : StandardSingularOscillatorLibrary) (k : ℕ) :
    ∃ F M : RadialSystem, ∃ _h : RadialFacts (radialIndex 1 k) F M,
      (∀ positive, deficiency M positive = if k = 0 then 1 else 0) ∧
      radialIndex 1 k * (radialIndex 1 k + 1) = angularCoefficient 1 k := by
  obtain ⟨F, M, ⟨h⟩⟩ := library (radialIndex 1 k) (index_nonneg 1 k (coefficient_one_nonneg k))
  refine ⟨F, M, h, ?_, index_quadratic 1 k (coefficient_one_nonneg k)⟩
  intro positive
  simp only [h.deficiency_indices, index_one_limit_circle]

theorem monopole_radial_domains_signed (library : StandardSingularOscillatorLibrary)
    (q : ℤ) (hq : q = 1 ∨ q = -1) (k : ℕ) :
    ∃ F M : RadialSystem, ∃ _h : RadialFacts (radialIndex q k) F M,
      (∀ positive, deficiency M positive = if k = 0 then 1 else 0) ∧
      radialIndex q k * (radialIndex q k + 1) = angularCoefficient q k := by
  rcases hq with rfl | rfl
  · exact monopole_radial_domains library k
  · rw [index_opposite 1 k, coefficient_opposite 1 k]
    exact monopole_radial_domains library k

theorem monopole_endpoint_classification (k : ℕ) (F M : RadialSystem)
    (h : RadialFacts (radialIndex 1 k) F M) (z : ℂ) :
    Module.finrank ℂ (localSolutionSpace (Ioo 0 1) (angularCoefficient 1 k) z) =
      (if k = 0 then 2 else 1) ∧
    Module.finrank ℂ (localSolutionSpace (Ioi 1) (angularCoefficient 1 k) z) = 1 := by
  have hq := index_quadratic 1 k (coefficient_one_nonneg k)
  rw [← hq]
  constructor
  · simpa only [index_one_limit_circle] using h.origin_solution_dimension z
  · exact h.infinity_solution_dimension z

theorem monopole_radial_energy (n k : ℕ) :
    4 * n + 2 * radialIndex 1 k + 3 = shell 1 n k := by
  unfold radialIndex
  rw [coefficient_one]
  unfold shell
  norm_num
  have he : 1 + 4 * ((k : ℝ) ^ 2 + 2 * k + 1 / 2) = (2 * k + 1 + 1) ^ 2 - 1 := by ring
  rw [he]
  ring

theorem power_memLp_origin (α : ℝ) :
    MemLp (fun r : ℝ => (r ^ α : ℝ)) 2 (volume.restrict (Ioo 0 1)) ↔ -1 < 2 * α := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  have he : (fun r : ℝ => ‖r ^ α‖ ^ 2) =ᵐ[volume.restrict (Ioo 0 1)]
      fun r => r ^ (2 * α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hr.1.le]
    congr 1
    norm_num
    ring
  rw [integrable_congr he]
  exact intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)

theorem principal_branch_square_integrable (ell : ℝ) (hell : 0 ≤ ell) :
    MemLp (fun r : ℝ => r ^ (ell + 1)) 2 (volume.restrict (Ioo 0 1)) := by
  rw [power_memLp_origin]
  linarith

theorem singular_branch_square_integrable_iff (ell : ℝ) :
    MemLp (fun r : ℝ => r ^ (-ell)) 2 (volume.restrict (Ioo 0 1)) ↔ ell < 1 / 2 := by
  rw [power_memLp_origin]
  constructor <;> intro h <;> linarith

theorem lowest_domain_boundary (library : StandardSingularOscillatorLibrary) :
    ∃ F M : RadialSystem, ∃ _h : RadialFacts MagHK.Monopole.ell F M,
      (∀ positive, deficiency M positive = 1) ∧
      ∀ ψ, ψ ∈ F.domain ↔ ∃ u : ℝ → ℂ,
        (∀ᵐ r ∂radialMeasure, ψ r = u r) ∧ MaximalDomain (1 / 2) u ∧
          Tendsto (boundary MagHK.Monopole.ell u) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨F, M, ⟨h⟩⟩ := library MagHK.Monopole.ell MagHK.Monopole.lowest_sector_limit_circle.1.le
  refine ⟨F, M, h, ?_, ?_⟩
  · intro positive
    simp only [h.deficiency_indices, MagHK.Monopole.lowest_sector_limit_circle.2, ite_true]
  · intro ψ
    simpa only [MagHK.Monopole.ell_quadratic,
      MagHK.Monopole.lowest_sector_limit_circle.2, true_implies, FriedrichsBoundary] using h.domain_characterization ψ

abbrev AngularIndex (q : ℤ) := Σ k : ℕ, Fin (2 * k + q.natAbs + 1)
abbrev AngularState := Lp ℂ 2 sphereMeasure

/-- A full monopole-harmonic resolution on actual angular L², including the
literal angular differential equation and finite endpoint energy. -/
structure AngularResolution (q : ℤ) where
  harmonic : AngularIndex q → Angle → ℂ
  solution : ∀ a, AngularSolution ((q : ℝ) / 2) (angularCoefficient q a.1) (harmonic a)
  state : AngularIndex q → AngularState
  represented : ∀ a, ∀ᵐ p ∂sphereMeasure, state a p = harmonic a p
  orthonormal : Orthonormal ℂ state
  complete : Dense (Submodule.span ℂ (range state) : Set AngularState)

def SeparatedRepresentative (Y : Angle → ℂ) (u : RadialState) (ψ : State) : Prop :=
  ∀ᵐ x ∂chartMeasure, ψ x = u x.1 / (x.1 : ℂ) * Y x.2

/-- Exact radial-subspace identification, including both operator domains. -/
structure RadialRestriction (H : System) (F : RadialSystem) (Y : Angle → ℂ) : Prop where
  represented : ∀ u : RadialState, ∃ ψ : State, SeparatedRepresentative Y u ψ
  domain : ∀ u ψ, SeparatedRepresentative Y u ψ → (u ∈ F.domain ↔ ψ ∈ H.domain)
  action : ∀ u ψ (hrep : SeparatedRepresentative Y u ψ) (hu : u ∈ F.domain),
    SeparatedRepresentative Y (F.map ⟨u, hu⟩)
      (H.map ⟨ψ, (domain u ψ hrep).mp hu⟩)

/-- The standard polar separation unitary and Friedrichs restriction theorem.
The radial and angular equations and both actual integral-form realizations
are arguments. No selected mode or energy is singled out. -/
def StandardRadialReductionLibrary : Prop :=
  ∀ q (H : System), OneBodyFacts H q → ∀ ell (F M : RadialSystem),
    0 ≤ ell → RadialFacts ell F M → ∀ Y : Angle → ℂ,
    AngularSolution ((q : ℝ) / 2) (ell * (ell + 1)) Y → RadialRestriction H F Y

theorem monopole_radial_restriction (oscillator : StandardSingularOscillatorLibrary)
    (reduction : StandardRadialReductionLibrary) (q : ℤ) (hq : q = 1 ∨ q = -1)
    (H : System) (hH : OneBodyFacts H q) (Y : AngularResolution q) (a : AngularIndex q) :
    ∃ F M : RadialSystem, ∃ _h : RadialFacts (radialIndex q a.1) F M,
      RadialRestriction H F (Y.harmonic a) := by
  obtain ⟨F, M, hF, _, hcoeff⟩ := monopole_radial_domains_signed oscillator q hq a.1
  have hn : 0 ≤ radialIndex q a.1 := by
    rcases hq with rfl | rfl
    · exact index_nonneg 1 a.1 (coefficient_one_nonneg a.1)
    · rw [index_opposite 1 a.1]
      exact index_nonneg 1 a.1 (coefficient_one_nonneg a.1)
  refine ⟨F, M, hF, reduction q H hH _ F M hn hF (Y.harmonic a) ?_⟩
  simpa only [hcoeff] using Y.solution a

/-- The regular separated core of the minimal punctured-space operator.
Unlike `OneCore`, it has no cutoff at the polar axes. Compact radial support
omits precisely the radial origin and infinity. -/
def HarmonicCore (q : ℤ) (Y : AngularResolution q) (f : Chart → ℂ) : Prop :=
  ∃ s : Finset (AngularIndex q), ∃ u : AngularIndex q → ℝ → ℂ,
    (∀ a ∈ s, RadialCore (u a)) ∧
    ∀ x, f x = ∑ a ∈ s, (u a x.1 / (x.1 : ℂ)) * Y.harmonic a x.2

structure MinimalOneBodyFacts (q : ℤ) (Y : AngularResolution q) (M : System) : Prop where
  graph : ∀ ψ η, (∃ h : ψ ∈ M.domain, M.map ⟨ψ, h⟩ = η) ↔
    MinimalGraph chartMeasure (HarmonicCore q Y) (oneExpression q) ψ η
  deficiency_indices : ∀ positive, deficiency M positive =
    ∑' k : ℕ, if angularCoefficient q k < 3 / 4 then 2 * k + q.natAbs + 1 else 0

/-- The universal angular harmonic resolution and direct-sum adjoint-domain
theorem. The radial deficiency threshold is 3/4. This theorem applies to all
integer charges, and its initial operator graph is explicitly given above.
The graph closure of regular harmonic finite sums is the closure of smooth
compactly supported bundle sections on punctured space. -/
def StandardAngularEndpointLibrary : Prop :=
  ∀ q : ℤ, ∃ Y : AngularResolution q, ∃ M : System, MinimalOneBodyFacts q Y M

theorem one_charge_deficiency_sum :
    (∑' k : ℕ, if angularCoefficient 1 k < 3 / 4 then 2 * k + (1 : ℤ).natAbs + 1 else 0) = 2 := by
  rw [tsum_eq_single 0]
  · norm_num [coefficient_one]
  · intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hc : ¬ angularCoefficient 1 k < 3 / 4 := by
      rw [coefficient_one]
      nlinarith [sq_nonneg (k : ℝ)]
    simp only [hc, ite_false]

theorem opposite_charge_deficiency_sum :
    (∑' k : ℕ, if angularCoefficient (-1) k < 3 / 4 then 2 * k + (-1 : ℤ).natAbs + 1 else 0) = 2 := by
  simpa only [coefficient_opposite, Int.natAbs_neg] using one_charge_deficiency_sum

theorem monopole_deficiency_indices (library : StandardAngularEndpointLibrary) (q : ℤ)
    (hq : q = 1 ∨ q = -1) :
    ∃ Y : AngularResolution q, ∃ M : System, MinimalOneBodyFacts q Y M ∧
      deficiency M true = 2 ∧ deficiency M false = 2 := by
  obtain ⟨Y, M, hM⟩ := library q
  refine ⟨Y, M, hM, ?_, ?_⟩
  all_goals
    rw [hM.deficiency_indices]
    rcases hq with rfl | rfl
    · exact one_charge_deficiency_sum
    · exact opposite_charge_deficiency_sum

def FormDomain (q : ℤ) (W : Chart × Chart → ℝ) : Set PairState :=
  {ψ | ψ ∈ fermionSubspace ∧
    ∃ f u, FormApproximation pairMeasure PairCore (pairForm q W) ψ f u}

/-- KLMN form-domain equality for arbitrary infinitesimally form-bounded
nonnegative symmetric multipliers. The domains are the actual integral-form
closures, not metadata attached to a spectrum. -/
def StandardFormDomainLibrary : Prop :=
  ∀ q W, Measurable W → (∀ p, W (p.2, p.1) = W p) → (∀ p, 0 ≤ W p) →
    InfinitesimalFormBound q W → FormDomain q W = FormDomain q 0

theorem coulomb_same_form_domain (forms : StandardFormDomainLibrary)
    (hardy : StandardCoulombFormLibrary) (q : ℤ) :
    FormDomain q coulomb = FormDomain q 0 :=
  forms q coulomb coulomb_measurable coulomb_symmetric coulomb_nonnegative (hardy q)

theorem magnetic_domains_equal (forms : StandardFormDomainLibrary)
    (hardy : StandardCoulombFormLibrary) (q : ℤ) (S₀ S : MagneticFormSystem)
    (F₀ F : FermionSystem) (h₀ : MagneticFormFacts S₀ F₀ q 0)
    (h : MagneticFormFacts S F q coulomb) : S.domain = S₀.domain := by
  ext ψ
  rw [h.domain_closure, h₀.domain_closure]
  exact Set.ext_iff.mp (coulomb_same_form_domain forms hardy q) ψ

theorem form_domain_and_compactness (forms : StandardFormDomainLibrary)
    (hardy : StandardCoulombFormLibrary) (q : ℤ) (F₀ F : FermionSystem)
    (h₀ : FermionFacts F₀ q 0) (h : FermionFacts F q coulomb) :
    FormDomain q coulomb = FormDomain q 0 ∧ OperatorModel.CompactResolvent F₀ ∧
      OperatorModel.CompactResolvent F :=
  ⟨coulomb_same_form_domain forms hardy q, h₀.compact_resolvent, h.compact_resolvent⟩

end MagHK.MonopoleEndpointDomains
