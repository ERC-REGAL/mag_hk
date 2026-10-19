import MagHK.MonopoleHilbert
import MagHK.MonopoleRadialDomain
import MagHK.MonopoleAngular
import MagHK.OperatorCompactness

/-!
The monopole oscillator as the Friedrichs operator on actual section L².
All external premises below are uniform operator-theory results. The operator
graph is identified with the closure of a literal magnetic sesquilinear form.
The core is periodic in azimuth, not subject to a Dirichlet condition at an
artificial azimuth cut. The concrete angular equations, radial equation and
finite-energy endpoint bounds are supplied by checked calculations.

The all-charge angular spectral input is the Wu–Yang monopole harmonic
theorem for integral twice-charge. Its radial part is the Friedrichs singular
oscillator spectrum. Our convention −i∇+A reverses Wu–Yang's charge sign.
-/
noncomputable section
namespace MagHK.MonopoleRealization
open MeasureTheory Set Filter
open MagHK.Monopole MagHK.MonopoleTrial MagHK.MonopoleRadialDomain MagHK.MonopoleAngular
open scoped ComplexConjugate ContDiff Topology
set_option maxHeartbeats 1000000

def Dr (f : Chart → ℂ) (x : Chart) : ℂ := deriv (fun r => f (r, x.2)) x.1
def Dmu (f : Chart → ℂ) (x : Chart) : ℂ := Dμ (fun p => f (x.1, p)) x.2
def Dphi (f : Chart → ℂ) (x : Chart) : ℂ := Dφ (fun p => f (x.1, p)) x.2
def magneticPhi (q : ℤ) (f : Chart → ℂ) (x : Chart) : ℂ :=
  -Complex.I * Dphi f x + (northCoefficient q x.2.1 : ℂ) * f x

def formDensity (q : ℤ) (f g : Chart → ℂ) (x : Chart) : ℂ :=
  conj (Dr f x) * Dr g x + ((1 - x.2.1 ^ 2) / x.1 ^ 2 : ℝ) *
    conj (Dmu f x) * Dmu g x +
    conj (magneticPhi q f x) * magneticPhi q g x /
      (x.1 ^ 2 * (1 - x.2.1 ^ 2) : ℝ) +
    (x.1 ^ 2 : ℝ) * conj (f x) * g x

def oneForm (q : ℤ) (f g : Chart → ℂ) : ℂ :=
  ∫ x, formDensity q f g x ∂chartMeasure

def oneExpression (q : ℤ) (f : Chart → ℂ) (x : Chart) : ℂ :=
  -Dr (Dr f) x - (2 / x.1 : ℝ) * Dr f x +
    angularExpression ((q : ℝ) / 2) (fun p => f (x.1, p)) x.2 / (x.1 ^ 2 : ℝ) +
    (x.1 ^ 2 : ℝ) * f x

/-- A genuine periodic chart core, supported away from the radial origin and
both polar axes. The missing axes have zero form capacity. -/
def OneCore (f : Chart → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
  (∀ r μ, Function.Periodic (fun φ => f (r, μ, φ)) (2 * Real.pi)) ∧
  ∃ δ R : ℝ, 0 < δ ∧ ∀ x, f x ≠ 0 →
    δ ≤ x.1 ∧ x.1 ≤ R ∧ -1 + δ ≤ x.2.1 ∧ x.2.1 ≤ 1 - δ

def pairForm (q : ℤ) (W : Chart × Chart → ℝ)
    (f g : Chart × Chart → ℂ) : ℂ :=
  ∫ p, formDensity q (fun x => f (x, p.2)) (fun x => g (x, p.2)) p.1 +
    formDensity q (fun y => f (p.1, y)) (fun y => g (p.1, y)) p.2 +
    (W p : ℂ) * conj (f p) * g p ∂pairMeasure

def pairExpression (q : ℤ) (W : Chart × Chart → ℝ)
    (f : Chart × Chart → ℂ) (p : Chart × Chart) : ℂ :=
  oneExpression q (fun x => f (x, p.2)) p.1 +
    oneExpression q (fun y => f (p.1, y)) p.2 + (W p : ℂ) * f p

def PairCore (f : Chart × Chart → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x y, f (y, x) = -f (x, y)) ∧
  (∀ r μ y, Function.Periodic (fun φ => f ((r, μ, φ), y)) (2 * Real.pi)) ∧
  ∃ δ R : ℝ, 0 < δ ∧ ∀ p, f p ≠ 0 →
    (δ ≤ p.1.1 ∧ p.1.1 ≤ R ∧ -1 + δ ≤ p.1.2.1 ∧ p.1.2.1 ≤ 1 - δ) ∧
    (δ ≤ p.2.1 ∧ p.2.1 ≤ R ∧ -1 + δ ≤ p.2.2.1 ∧ p.2.2.1 ≤ 1 - δ)

/-- Form-norm approximation is stated using actual core functions and actual
L² convergence. Its Cauchy condition uses the literal integral form. -/
def FormApproximation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (core : (X → ℂ) → Prop) (form : (X → ℂ) → (X → ℂ) → ℂ)
    (ψ : Lp ℂ 2 μ) (f : ℕ → X → ℂ) (u : ℕ → Lp ℂ 2 μ) : Prop :=
  (∀ n, core (f n)) ∧ (∀ n, ∀ᵐ x ∂μ, u n x = f n x) ∧
  Tendsto u atTop (𝓝 ψ) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
    (form (f n - f m) (f n - f m)).re < ε

/-- The representation theorem characterization of the Friedrichs graph.
Both the form closure and its pairing with every core test are explicit. -/
def FriedrichsGraph {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (core : (X → ℂ) → Prop) (form : (X → ℂ) → (X → ℂ) → ℂ)
    (ψ η : Lp ℂ 2 μ) : Prop :=
  ∃ f u, FormApproximation μ core form ψ f u ∧
    ∀ ζ, core ζ → Tendsto (fun n => form ζ (f n)) atTop
      (𝓝 (∫ x, conj (ζ x) * η x ∂μ))

def EigenFunction (H : System) (E : ℝ) (f : Chart → ℂ) : Prop :=
  ∃ ψ : State, (∀ᵐ x ∂chartMeasure, ψ x = f x) ∧ OperatorModel.Eigen H E ψ

structure AngularSolution (g lam : ℝ) (Y : Angle → ℂ) : Prop where
  smooth : ContDiffOn ℝ 2 Y (Ioo (-1) 1 ×ˢ univ)
  periodic : ∀ μ, Function.Periodic (fun φ => Y (μ, φ)) (2 * Real.pi)
  mass_integrable : Integrable (fun p => Complex.normSq (Y p)) sphereMeasure
  mass_positive : 0 < ∫ p, Complex.normSq (Y p) ∂sphereMeasure
  energy_integrable : Integrable (angularEnergy g Y) sphereMeasure
  equation : ∀ p, p.1 ∈ Ioo (-1) 1 → angularExpression g Y p = (lam : ℂ) * Y p

structure RadialSolution (lam E : ℝ) (u : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 u (Ioi 0)
  bounded_origin : ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |u r| ≤ C
  mass_integrable : Integrable (fun r => u r ^ 2) radialVolume
  mass_positive : 0 < ∫ r, u r ^ 2 ∂radialVolume
  energy_integrable : Integrable
    (fun r => deriv u r ^ 2 + (lam / r ^ 2 + r ^ 2) * u r ^ 2) radialVolume
  equation : ∀ r, 0 < r → -deriv (deriv u) r - 2 / r * deriv u r +
    (lam / r ^ 2 + r ^ 2) * u r = E * u r

def shell (q : ℤ) (n k : ℕ) : ℝ :=
  4 * n + 2 + Real.sqrt ((2 * k + (q.natAbs : ℝ) + 1) ^ 2 - (q : ℝ) ^ 2)

structure OneBodyFacts (H : System) (q : ℤ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint H
  compact_resolvent : OperatorModel.CompactResolvent H
  friedrichs : ∀ ψ η, (∃ hψ : ψ ∈ H.domain, H.map ⟨ψ, hψ⟩ = η) ↔
    FriedrichsGraph chartMeasure OneCore (oneForm q) ψ η
  weak_equation : ∀ ψ (hψ : ψ ∈ H.domain) ζ, OneCore ζ →
    (∫ x, conj (ζ x) * H.map ⟨ψ, hψ⟩ x ∂chartMeasure) =
      ∫ x, conj (oneExpression q ζ x) * ψ x ∂chartMeasure
  spectrum_eq : ∀ E, E ∈ OperatorModel.spectrum H ↔ ∃ n k, E = shell q n k
  unique_shell_multiplicity : ∀ n k,
    (∀ n' k', shell q n' k' = shell q n k → n' = n ∧ k' = k) →
    OperatorModel.multiplicity H (shell q n k) = 2 * k + q.natAbs + 1
  separated_solution : ∀ lam E u Y, 0 ≤ lam →
    AngularSolution ((q : ℝ) / 2) lam Y → RadialSolution lam E u →
    EigenFunction H E (fun x => (u x.1 : ℂ) * Y x.2)

/-- Universal monopole harmonic decomposition, singular oscillator solution,
and finite-energy weak-to-Friedrichs realization. No chosen state appears in
this premise. Unique-shell multiplicity avoids false multiplicity claims at
accidental coincidences, such as those of the zero-charge oscillator. -/
def StandardMonopoleLibrary : Prop := ∀ q : ℤ, ∃ H : System, OneBodyFacts H q

theorem shell_one (n k : ℕ) : shell 1 n k = shellEnergy n k := by
  unfold shell shellEnergy
  norm_num
  congr 2
  ring

theorem one_body_lowest (H : System) (hH : OneBodyFacts H 1) :
    (2 + Real.sqrt 3) ∈ OperatorModel.spectrum H ∧
    (∀ E ∈ OperatorModel.spectrum H, 2 + Real.sqrt 3 ≤ E) ∧
    OperatorModel.multiplicity H (2 + Real.sqrt 3) = 2 ∧
    (∀ E ∈ OperatorModel.spectrum H, E ≠ 2 + Real.sqrt 3 → 2 + Real.sqrt 15 ≤ E) := by
  have h00 : shell 1 0 0 = 2 + Real.sqrt 3 := by rw [shell_one, lowest_shell_energy]
  refine ⟨(hH.spectrum_eq _).mpr ⟨0, 0, h00.symm⟩, ?_, ?_, ?_⟩
  · intro E hE
    obtain ⟨n, k, rfl⟩ := (hH.spectrum_eq E).mp hE
    rw [shell_one]
    exact shellEnergy_ground_bound n k
  · rw [← h00]
    simpa using hH.unique_shell_multiplicity 0 0 (by
      intro n k he
      by_contra hne
      have hn : n ≠ 0 ∨ k ≠ 0 := by tauto
      have h := first_excited_shell_bound n k hn
      rw [← shell_one, he, h00] at h
      have hg := gap_positive
      unfold freeGap at hg
      linarith)
  · intro E hE hne
    obtain ⟨n, k, rfl⟩ := (hH.spectrum_eq E).mp hE
    rw [shell_one]
    apply first_excited_shell_bound n k
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    exact hne h00

def frameDerivative (q : ℤ) (k : Fin 3) (f : Chart → ℂ) (x : Chart) : ℂ :=
  if k = 0 then -Complex.I * Dr f x
  else if k = 1 then Complex.I * (Real.sqrt (1 - x.2.1 ^ 2) / x.1 : ℝ) * Dmu f x
  else magneticPhi q f x / (x.1 * Real.sqrt (1 - x.2.1 ^ 2) : ℝ)

def pairFrameDerivative (q : ℤ) (i : Fin 2) (k : Fin 3)
    (f : Chart × Chart → ℂ) (p : Chart × Chart) : ℂ :=
  if i = 0 then frameDerivative q k (fun x => f (x, p.2)) p.1
  else frameDerivative q k (fun y => f (p.1, y)) p.2

structure MagneticFormSystem where
  domain : Submodule ℂ PairState
  pi : Fin 2 → Fin 3 → domain →ₗ[ℂ] PairState

def fullPotential (W : Chart × Chart → ℝ) (p : Chart × Chart) : ℝ :=
  p.1.1 ^ 2 + p.2.1 ^ 2 + W p

def formPairing (S : MagneticFormSystem) (W : Chart × Chart → ℝ)
    (ψ ζ : S.domain) : ℂ :=
  (∑ i : Fin 2, ∑ k : Fin 3, inner ℂ (S.pi i k ψ) (S.pi i k ζ)) +
    ∫ p, (fullPotential W p : ℂ) * conj ((ψ : PairState) p) * (ζ : PairState) p ∂pairMeasure

def symmetricMultiplier (χ : ℝ → ℝ) (p : Chart × Chart) : ℝ := χ p.1.1 + χ p.2.1

/-- General weighted Sobolev closure and multiplier product rules. The weak
covariant derivatives are pinned to the literal frame derivatives on the
core and by closure, and the operator identity is the representation theorem.
No continuity equation or current conclusion is assumed. -/
structure MagneticFormFacts (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) : Prop where
  domain_closure : ∀ ψ : PairState, ψ ∈ S.domain ↔
    ψ ∈ fermionSubspace ∧ ∃ f u, FormApproximation pairMeasure PairCore (pairForm q W) ψ f u
  core_domain : ∀ f, PairCore f → ∃ ψ : S.domain, ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = f p
  core_pi : ∀ f, PairCore f → ∀ ψ : S.domain,
    (∀ᵐ p ∂pairMeasure, (ψ : PairState) p = f p) →
    ∀ i k, ∀ᵐ p ∂pairMeasure, S.pi i k ψ p = pairFrameDerivative q i k f p
  pi_closure : ∀ ψ : S.domain, ∃ f : ℕ → Chart × Chart → ℂ, ∃ u : ℕ → S.domain,
    FormApproximation pairMeasure PairCore (pairForm q W) (ψ : PairState) f (fun n => (u n : PairState)) ∧
    ∀ i k, Tendsto (fun n => S.pi i k (u n)) atTop (𝓝 (S.pi i k ψ))
  potential_integrable : ∀ ψ ζ : S.domain,
    Integrable (fun p => (fullPotential W p : ℂ) * conj ((ψ : PairState) p) * (ζ : PairState) p)
      pairMeasure
  operator_domain : ∀ ψ : FermionState, ψ ∈ F.domain → (ψ : PairState) ∈ S.domain
  operator_form : ∀ ψ (hψ : ψ ∈ F.domain) ζ,
    formPairing S W ⟨(ψ : PairState), operator_domain ψ hψ⟩ ζ =
      inner ℂ (((F.map ⟨ψ, hψ⟩ : FermionState) : PairState)) (ζ : PairState)
  symmetric_multiplier : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
    Function.support χ ⊆ Ioi 0 → ∀ ψ : S.domain, ∃ ζ : S.domain,
      (∀ᵐ p ∂pairMeasure, (ζ : PairState) p = (symmetricMultiplier χ p : ℂ) * (ψ : PairState) p) ∧
      ∀ i k, ∀ᵐ p ∂pairMeasure, S.pi i k ζ p =
        (symmetricMultiplier χ p : ℂ) * S.pi i k ψ p -
          if k = 0 then Complex.I * ((deriv χ (if i = 0 then p.1.1 else p.2.1) : ℝ) : ℂ) *
            (ψ : PairState) p else 0
  exchange : ∀ ψ : S.domain, ∀ i k, ∀ᵐ p ∂pairMeasure,
    S.pi i k ψ (p.2, p.1) = -S.pi i.rev k ψ p

structure FermionFacts (F : FermionSystem) (q : ℤ) (W : Chart × Chart → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint F
  compact_resolvent : OperatorModel.CompactResolvent F
  friedrichs : ∀ ψ η,
    (∃ hψ : ψ ∈ F.domain, F.map ⟨ψ, hψ⟩ = η) ↔
      FriedrichsGraph pairMeasure PairCore (pairForm q W) (ψ : PairState) (η : PairState)
  weak_equation : ∀ ψ (hψ : ψ ∈ F.domain) ζ, PairCore ζ →
    (∫ p, conj (ζ p) * ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState) p ∂pairMeasure) =
      ∫ p, conj (pairExpression q W ζ p) * (ψ : PairState) p ∂pairMeasure
  form_realization : ∃ S : MagneticFormSystem, MagneticFormFacts S F q W

def GroundState (F : FermionSystem) (E : ℝ) (f : Chart × Chart → ℂ) : Prop :=
  (∃ ψ : FermionState, (∀ᵐ p ∂pairMeasure, (ψ : PairState) p = f p) ∧
    OperatorModel.Eigen F E ψ) ∧
  (∀ e ∈ OperatorModel.spectrum F, E ≤ e) ∧ OperatorModel.multiplicity F E = 1

def SpectralGap (F : FermionSystem) (E δ : ℝ) : Prop :=
  ∀ e ∈ OperatorModel.spectrum F, e ≠ E → E + δ ≤ e

/-- Exterior-square filling for any two-dimensional lowest one-particle
eigenspace. This is independent of the chosen charge, orbitals and energies. -/
def StandardExteriorLibrary : Prop :=
  ∀ q (H : System), OneBodyFacts H q → ∀ e δ (f g : Chart → ℂ), 0 < δ →
    (∀ E ∈ OperatorModel.spectrum H, e ≤ E) →
    OperatorModel.multiplicity H e = 2 →
    (∀ E ∈ OperatorModel.spectrum H, E ≠ e → e + δ ≤ E) →
    EigenFunction H e f → EigenFunction H e g →
    MagHK.Slater.OrthonormalPair chartMeasure f g →
    ∃ F : FermionSystem, FermionFacts F q 0 ∧
      GroundState F (2 * e) (determinant f g) ∧ SpectralGap F (2 * e) δ

/-- First and second variational levels count multiplicity. The strict
inequality implies a one-dimensional ground eigenspace. -/
structure FirstTwoLevels (F : FermionSystem) (E₀ E₁ : ℝ) : Prop where
  ground_eigen : ∃ ψ, OperatorModel.Eigen F E₀ ψ
  bottom : ∀ E ∈ OperatorModel.spectrum F, E₀ ≤ E
  second_above : ∀ E ∈ OperatorModel.spectrum F, E ≠ E₀ → E₁ ≤ E
  simple_of_lt : E₀ < E₁ → OperatorModel.multiplicity F E₀ = 1

def InfinitesimalFormBound (q : ℤ) (W : Chart × Chart → ℝ) : Prop :=
  (∀ f, PairCore f → Integrable (fun p => W p * Complex.normSq (f p)) pairMeasure) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f, PairCore f →
    |∫ p, W p * Complex.normSq (f p) ∂pairMeasure| ≤
      ε * (pairForm q 0 f f).re + C * (∫ p, Complex.normSq (f p) ∂pairMeasure)

/-- The magnetic Hardy/diamagnetic form bound for the literal Euclidean
Coulomb multiplier, uniform in the integral monopole charge. -/
def StandardCoulombFormLibrary : Prop :=
  ∀ q : ℤ, InfinitesimalFormBound q coulomb

/-- Closed-form perturbation, compactness of the confining form embedding,
and the first two min–max inequalities for any nonnegative form perturbation.
The trial vector is arbitrary and its expectation is an actual integral. -/
def StandardPositivePerturbationLibrary : Prop :=
  ∀ q W, Measurable W → (∀ p, W (p.2, p.1) = W p) → (∀ p, 0 ≤ W p) →
    InfinitesimalFormBound q W →
    ∀ (F₀ : FermionSystem) e δ f, FermionFacts F₀ q 0 → GroundState F₀ e f →
      0 < δ → SpectralGap F₀ e δ →
      (∫ p, Complex.normSq (f p) ∂pairMeasure) = 1 →
      Integrable (fun p => W p * Complex.normSq (f p)) pairMeasure →
      ∃ F : FermionSystem, ∃ E₀ E₁ : ℝ, FermionFacts F q W ∧ FirstTwoLevels F E₀ E₁ ∧
        E₀ ≤ e + (∫ p, W p * Complex.normSq (f p) ∂pairMeasure) ∧ e + δ ≤ E₁

private theorem normSq_integrable (Y : Angle → ℂ)
    (h : Integrable (fun p => star (Y p) * Y p) sphereMeasure) :
    Integrable (fun p => Complex.normSq (Y p)) sphereMeasure := by
  have hi : Integrable (fun p => (star (Y p) * Y p).re) sphereMeasure := h.re
  apply hi.congr
  exact ae_of_all _ (fun p => by
    dsimp only
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re])

private theorem normSq_integral (Y : Angle → ℂ)
    (hi : Integrable (fun p => star (Y p) * Y p) sphereMeasure)
    (h : (∫ p, star (Y p) * Y p ∂sphereMeasure) = 1) :
    (∫ p, Complex.normSq (Y p) ∂sphereMeasure) = 1 := by
  calc
    _ = ∫ p, (star (Y p) * Y p).re ∂sphereMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by
        dsimp only
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re])
    _ = (∫ p, star (Y p) * Y p ∂sphereMeasure).re := integral_re hi
    _ = 1 := by rw [h]; rfl

theorem plus_angular_solution : AngularSolution (1 / 2) (1 / 2) Yplus := by
  refine ⟨Yplus_contDiffOn, Yplus_periodic,
    normSq_integrable _ doublet_orthonormal.integrable_ff, ?_,
    Yplus_energy_integrable, ?_⟩
  · rw [normSq_integral _ doublet_orthonormal.integrable_ff doublet_orthonormal.norm_f]
    norm_num
  · intro p hp
    simpa using Yplus_equation p hp

theorem minus_angular_solution : AngularSolution (1 / 2) (1 / 2) Yminus := by
  refine ⟨Yminus_contDiffOn, Yminus_periodic,
    normSq_integrable _ doublet_orthonormal.integrable_gg, ?_,
    Yminus_energy_integrable, ?_⟩
  · rw [normSq_integral _ doublet_orthonormal.integrable_gg doublet_orthonormal.norm_g]
    norm_num
  · intro p hp
    simpa using Yminus_equation p hp

theorem trial_radial_solution : RadialSolution (1 / 2) (2 + Real.sqrt 3) radialOrbital := by
  refine ⟨radialOrbital_contDiffOn, radialOrbital_bounded_origin,
    radialOrbital_integrable_radialVolume, ?_, ?_, ?_⟩
  · rw [radialOrbital_normalized_radialVolume]
    norm_num
  · convert radialOrbital_finite_energy using 1
    funext r
    congr 2
    ring
  · intro r hr
    convert radialOrbital_eigen_equation r hr using 1
    ring

theorem trial_orbital_eigenfunctions (H : System) (hH : OneBodyFacts H 1) :
    EigenFunction H (2 + Real.sqrt 3) orbitalPlus ∧
      EigenFunction H (2 + Real.sqrt 3) orbitalMinus := by
  constructor
  · exact hH.separated_solution (1 / 2) _ _ _ (by norm_num)
      (by simpa using plus_angular_solution) trial_radial_solution
  · exact hH.separated_solution (1 / 2) _ _ _ (by norm_num)
      (by simpa using minus_angular_solution) trial_radial_solution

/-- The explicit determinant occupies the full lowest monopole doublet.
Its free two-fermion ground energy and gap are derived from the all-shell
spectrum and the checked actual separated solutions. -/
theorem free_ground_state (monopole : StandardMonopoleLibrary)
    (exterior : StandardExteriorLibrary) :
    ∃ H : System, ∃ F : FermionSystem, OneBodyFacts H 1 ∧ FermionFacts F 1 0 ∧
      GroundState F (2 * (2 + Real.sqrt 3)) trialWave ∧
      SpectralGap F (2 * (2 + Real.sqrt 3)) freeGap := by
  obtain ⟨H, hH⟩ := monopole 1
  obtain ⟨_, hbottom, hmult, hgap⟩ := one_body_lowest H hH
  obtain ⟨hp, hm⟩ := trial_orbital_eigenfunctions H hH
  have hegap : 2 + Real.sqrt 3 + freeGap = 2 + Real.sqrt 15 := by
    unfold freeGap
    ring
  obtain ⟨F, hF, hground, hfgap⟩ := exterior 1 H hH (2 + Real.sqrt 3) freeGap
    orbitalPlus orbitalMinus gap_positive hbottom hmult
      (by simpa only [hegap] using hgap) hp hm orbital_pair_orthonormal
  exact ⟨H, F, hH, hF, hground, hfgap⟩

end MagHK.MonopoleRealization
