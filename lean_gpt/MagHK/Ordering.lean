import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial ordering in Appendix A

The calculations and spectral-order deductions below are proved in Lean.
The interface `RadialOrderingData` records the analytic input from closed
quadratic forms and Sturm theory. It does not assert spectral ordering.
`DiscreteSpectralAssembly` records the standard direct-sum and isolated
discrete-spectrum results. See OrderingNotes.txt for the scope of this file.
-/

noncomputable section

namespace MagHK.Ordering

def radialExpression (m a v r u du ddu : ℝ) : ℝ :=
  -ddu - du / r + ((m / r + a) ^ 2 + v) * u

def riccatiPotential (U dU a r : ℝ) : ℝ :=
  U ^ 2 - dU - U / r - a ^ 2

/-- The product rule for `D*D`, applied to the two-jet of a test function. -/
theorem factorization_DstarD (U dU a r u du ddu : ℝ) :
    -(ddu + dU * u + U * du) - (du + U * u) / r +
        U * (du + U * u) =
      radialExpression 0 a (riccatiPotential U dU a r) r u du ddu := by
  unfold radialExpression riccatiPotential
  ring

/-- The product rule for `DD*`, including the radial measure term. -/
theorem factorization_DDstar (U dU a r u du ddu : ℝ) (hr : r ≠ 0) :
    (-ddu - du / r + u / r ^ 2 + dU * u + U * du) +
        U * (-du - u / r + U * u) =
      radialExpression (-1) a (riccatiPotential U dU a r) r u du ddu +
        2 * (dU + a / r) * u := by
  unfold radialExpression riccatiPotential
  field_simp
  ring

/-- The pointwise integration-by-parts identity behind the positive
ground-state representation. The final four terms are the derivative of
`r*u*u'*w²`. Apply separately to the real and imaginary parts of `w`.
Integration removes this derivative for compactly supported test functions. -/
theorem ground_state_representation_algebra (r u du ddu w dw V lam : ℝ)
    (hr : r ≠ 0) (hu : -ddu - du / r + V * u = lam * u) :
    r * ((du * w + u * dw) ^ 2 + (V - lam) * (u * w) ^ 2) =
      r * u ^ 2 * dw ^ 2 +
        (u * du * w ^ 2 + r * du ^ 2 * w ^ 2 +
          r * u * ddu * w ^ 2 + 2 * r * u * du * w * dw) := by
  have h : r * (V * u - lam * u - ddu) = du := by
    field_simp at hu
    nlinarith
  have hm := congrArg (fun z : ℝ => u * w ^ 2 * z) h
  nlinarith only [hm]

theorem sector_difference (m a r : ℝ) (hr : r ≠ 0) :
    (m / r + a) ^ 2 - (-1 / r + a) ^ 2 =
      (m ^ 2 - 1 + 2 * (m + 1) * (r * a)) / r ^ 2 := by
  field_simp
  ring

theorem negative_sector_difference (k a r : ℝ) (hr : r ≠ 0) :
    (-k / r + a) ^ 2 - (-1 / r + a) ^ 2 =
      (k - 1) * (k + 1 - 2 * (r * a)) / r ^ 2 := by
  field_simp
  ring

theorem positive_sector_difference_pos (m a r : ℝ)
    (hr : 0 < r) (hm : 1 ≤ m) (ha : 0 < r * a) :
    0 < (m / r + a) ^ 2 - (-1 / r + a) ^ 2 := by
  rw [sector_difference m a r (ne_of_gt hr)]
  apply div_pos _ (sq_pos_of_pos hr)
  have hsq : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hterm : 0 < 2 * (m + 1) * (r * a) :=
    mul_pos (by linarith) ha
  linarith

theorem negative_sector_difference_pos (k a r : ℝ)
    (hr : 0 < r) (hk : 2 ≤ k) (ha : r * a < 1) :
    0 < (-k / r + a) ^ 2 - (-1 / r + a) ^ 2 := by
  rw [negative_sector_difference k a r (ne_of_gt hr)]
  exact div_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos hr)

theorem all_other_sector_difference_pos (m : ℤ) (a r : ℝ)
    (hr : 0 < r) (ha : 0 < r * a) (ha' : r * a < 1)
    (hm0 : m ≠ 0) (hm1 : m ≠ -1) :
    0 < ((m : ℝ) / r + a) ^ 2 - (-1 / r + a) ^ 2 := by
  have hc : 1 ≤ m ∨ m ≤ -2 := by omega
  rcases hc with h | h
  · exact positive_sector_difference_pos m a r hr (by exact_mod_cast h) ha
  · have hk : (2 : ℝ) ≤ -(m : ℝ) := by exact_mod_cast (show 2 ≤ -m by omega)
    simpa using negative_sector_difference_pos (-(m : ℝ)) a r hr hk ha'

/-- A strictly positive pointwise form correction is strictly positive on
every state of positive squared norm. No uniform lower bound is needed. -/
theorem strictly_positive_multiplier_integral {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (w g : α → ℝ)
    (hw : ∀ x, 0 < w x) (hg : ∀ x, 0 ≤ g x)
    (hgi : MeasureTheory.Integrable g μ)
    (hwgi : MeasureTheory.Integrable (fun x => w x * g x) μ)
    (hmass : 0 < ∫ x, g x ∂μ) : 0 < ∫ x, w x * g x ∂μ := by
  apply (MeasureTheory.integral_pos_iff_support_of_nonneg
    (fun x => mul_nonneg (le_of_lt (hw x)) (hg x)) hwgi).mpr
  have hs : Function.support (fun x => w x * g x) = Function.support g := by
    ext x
    change w x * g x ≠ 0 ↔ g x ≠ 0
    constructor
    · intro h hz
      exact h (by rw [hz, mul_zero])
    · intro h
      exact mul_ne_zero (ne_of_gt (hw x)) h
  rw [hs]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg hg hgi).mp hmass

/-- A densely defined operator can be represented by a linear map on its
domain. Density and closedness are needed by the analytic realization,
but the eigenvector-domain calculation needs only this structure. -/
structure DomainOperator (H : Type*) [AddCommGroup H] [Module ℝ H] where
  domain : Submodule ℝ H
  map : domain →ₗ[ℝ] H

/-- Domain membership in the supersymmetric eigenvector transfer is proved,
not silently discarded by treating the operators as everywhere defined. -/
theorem eigenvector_transfer {H : Type*} [AddCommGroup H] [Module ℝ H]
    (D A : DomainOperator H) (ψ : H) (E : ℝ)
    (hψ : ψ ∈ D.domain)
    (hDψ : D.map ⟨ψ, hψ⟩ ∈ A.domain)
    (hE : A.map ⟨D.map ⟨ψ, hψ⟩, hDψ⟩ = E • ψ) :
    ∃ hADψ : A.map ⟨D.map ⟨ψ, hψ⟩, hDψ⟩ ∈ D.domain,
      D.map ⟨A.map ⟨D.map ⟨ψ, hψ⟩, hDψ⟩, hADψ⟩ =
        E • D.map ⟨ψ, hψ⟩ := by
  have hADψ : A.map ⟨D.map ⟨ψ, hψ⟩, hDψ⟩ ∈ D.domain := by
    rw [hE]
    exact D.domain.smul_mem E hψ
  refine ⟨hADψ, ?_⟩
  have hs : (⟨A.map ⟨D.map ⟨ψ, hψ⟩, hDψ⟩, hADψ⟩ : D.domain) =
      E • (⟨ψ, hψ⟩ : D.domain) := by
    apply Subtype.ext
    exact hE
  rw [hs, map_smul]

/-- The form computation excluding all sectors other than zero and minus one. -/
theorem strict_form_comparison (E lam n q δ : ℝ)
    (hn : 0 < n) (hq : lam * n ≤ q) (hδ : 0 < δ)
    (hE : E * n = q + δ) : lam < E := by
  nlinarith

/-- The factorization computation for sector zero. `n` is the squared norm
of the eigenvector and `d` that of its image under the closed operator `D`.
The last hypothesis is the partner quadratic-form identity. -/
theorem zero_sector_energy (E lam n d : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hE : E * n = d)
    (hpartner : 0 < d → ∃ q δ : ℝ,
      lam * d ≤ q ∧ 0 < δ ∧ E * d = q + 2 * δ) :
    E = 0 ∨ lam < E := by
  by_cases hz : d = 0
  · left
    nlinarith
  · right
    have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    obtain ⟨q, δ, hq, hδ, heq⟩ := hpartner hp
    exact strict_form_comparison E lam d q (2 * δ) hp hq (by linarith) heq

/-- A quantitative version used in the oscillator example. -/
theorem zero_sector_quantitative_bound (E μ n d : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hE : E * n = d)
    (hE0 : E ≠ 0) (hpartner : μ * d ≤ E * d) : μ ≤ E := by
  have hdp : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by linarith
    have : E = 0 := by nlinarith
    exact hE0 this
  exact (mul_le_mul_iff_left₀ hdp).mp hpartner

/-- Analytic input from closed forms, first-order factorization, and the
positive radial ground-state representation. The norm and form identities
are the actual input, rather than an assumed ordering of the eigenvalues. -/
structure RadialOrderingData (eigen : ℤ → ℝ → Prop) (lam : ℝ) : Prop where
  lambda_pos : 0 < lam
  zero_state : eigen 0 0
  minus_one_state : eigen (-1) lam
  zero_form : ∀ E, eigen 0 E → ∃ n d : ℝ,
    0 < n ∧ 0 ≤ d ∧ E * n = d ∧
    (0 < d → ∃ q δ : ℝ, lam * d ≤ q ∧ 0 < δ ∧ E * d = q + 2 * δ)
  minus_one_form : ∀ E, eigen (-1) E → ∃ n q : ℝ,
    0 < n ∧ lam * n ≤ q ∧ E * n = q
  other_form : ∀ m E, m ≠ 0 → m ≠ -1 → eigen m E → ∃ n q δ : ℝ,
    0 < n ∧ lam * n ≤ q ∧ 0 < δ ∧ E * n = q + δ

theorem sector_zero_ordering {eigen : ℤ → ℝ → Prop} {lam E : ℝ}
    (h : RadialOrderingData eigen lam) (he : eigen 0 E) : E = 0 ∨ lam < E := by
  obtain ⟨n, d, hn, hd, hE, hp⟩ := h.zero_form E he
  exact zero_sector_energy E lam n d hn hd hE hp

theorem sector_minus_one_ordering {eigen : ℤ → ℝ → Prop} {lam E : ℝ}
    (h : RadialOrderingData eigen lam) (he : eigen (-1) E) : lam ≤ E := by
  obtain ⟨n, q, hn, hq, hE⟩ := h.minus_one_form E he
  nlinarith

theorem sector_other_ordering {eigen : ℤ → ℝ → Prop} {lam E : ℝ} {m : ℤ}
    (h : RadialOrderingData eigen lam) (hm0 : m ≠ 0) (hm1 : m ≠ -1)
    (he : eigen m E) : lam < E := by
  obtain ⟨n, q, δ, hn, hq, hδ, hE⟩ := h.other_form m E hm0 hm1 he
  exact strict_form_comparison E lam n q δ hn hq hδ hE

theorem sector_eigenvalue_classification {eigen : ℤ → ℝ → Prop} {lam E : ℝ} {m : ℤ}
    (h : RadialOrderingData eigen lam) (he : eigen m E) :
    (m = 0 ∧ E = 0) ∨ (m = -1 ∧ lam ≤ E) ∨ lam < E := by
  by_cases hm0 : m = 0
  · subst m
    rcases sector_zero_ordering h he with he0 | helam
    · exact Or.inl ⟨rfl, he0⟩
    · exact Or.inr (Or.inr helam)
  · by_cases hm1 : m = -1
    · subst m
      exact Or.inr (Or.inl ⟨rfl, sector_minus_one_ordering h he⟩)
    · exact Or.inr (Or.inr (sector_other_ordering h hm0 hm1 he))

theorem unique_sector_at_zero {eigen : ℤ → ℝ → Prop} {lam : ℝ} {m : ℤ}
    (h : RadialOrderingData eigen lam) (he : eigen m 0) : m = 0 := by
  rcases sector_eigenvalue_classification h he with ⟨hm, _⟩ | ⟨_, hle⟩ | hlt
  · exact hm
  · linarith [h.lambda_pos]
  · linarith [h.lambda_pos]

theorem unique_sector_at_lambda {eigen : ℤ → ℝ → Prop} {lam : ℝ} {m : ℤ}
    (h : RadialOrderingData eigen lam) (he : eigen m lam) : m = -1 := by
  rcases sector_eigenvalue_classification h he with ⟨_, he0⟩ | ⟨hm, _⟩ | hlt
  · linarith [h.lambda_pos]
  · exact hm
  · exact False.elim (lt_irrefl lam hlt)

/-- Standard consequences of the direct-sum spectral theorem and the absence
of essential spectrum below `Λ`. No ordering or gap at `lam` is assumed. -/
structure DiscreteSpectralAssembly (eigen : ℤ → ℝ → Prop)
    (spectrum : Set ℝ) (Λ : ℝ) : Prop where
  sector_in_spectrum : ∀ m E, eigen m E → E ∈ spectrum
  below_threshold : ∀ E ∈ spectrum, E < Λ → ∃ m, eigen m E
  isolated_below_threshold : ∀ E ∈ spectrum, E < Λ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ spectrum, |x - E| < ε → x = E

theorem planar_spectrum_below_second {eigen : ℤ → ℝ → Prop}
    {spectrum : Set ℝ} {lam Λ : ℝ}
    (h : RadialOrderingData eigen lam) (hs : DiscreteSpectralAssembly eigen spectrum Λ)
    (hlamΛ : lam < Λ) :
    ∀ E, E ∈ spectrum ∧ E ≤ lam ↔ E = 0 ∨ E = lam := by
  intro E
  constructor
  · rintro ⟨hE, hElam⟩
    obtain ⟨m, hm⟩ := hs.below_threshold E hE (lt_of_le_of_lt hElam hlamΛ)
    rcases sector_eigenvalue_classification h hm with ⟨_, he0⟩ | ⟨_, hle⟩ | hlt
    · exact Or.inl he0
    · exact Or.inr (le_antisymm hElam hle)
    · exact False.elim (not_lt_of_ge hElam hlt)
  · rintro (rfl | rfl)
    · exact ⟨hs.sector_in_spectrum 0 0 h.zero_state, le_of_lt h.lambda_pos⟩
    · exact ⟨hs.sector_in_spectrum (-1) _ h.minus_one_state, le_rfl⟩

theorem planar_strict_gap {eigen : ℤ → ℝ → Prop}
    {spectrum : Set ℝ} {lam Λ : ℝ}
    (h : RadialOrderingData eigen lam) (hs : DiscreteSpectralAssembly eigen spectrum Λ)
    (hlamΛ : lam < Λ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ E, lam < E → E < lam + ε → E ∉ spectrum := by
  obtain ⟨ε, hε, hiso⟩ := hs.isolated_below_threshold lam
    (hs.sector_in_spectrum (-1) lam h.minus_one_state) hlamΛ
  refine ⟨ε, hε, ?_⟩
  intro E hlamE hEε hE
  have heq : E = lam := hiso E hE (by rw [abs_of_pos (by linarith)]; linarith)
  linarith

/-- Multiplicity assembly at an energy supported in just one sector. The
first hypothesis is the standard direct-sum eigenspace decomposition.
Ground-state simplicity supplies the second hypothesis. -/
theorem single_sector_simplicity {eigen : ℤ → ℝ → Prop}
    (multiplicity : ℝ → ℕ) (sectorMultiplicity : ℤ → ℝ → ℕ)
    (E : ℝ) (m : ℤ)
    (assemble : (∀ n, eigen n E → n = m) →
      multiplicity E = sectorMultiplicity m E)
    (radial_simple : sectorMultiplicity m E = 1)
    (unique_sector : ∀ n, eigen n E → n = m) : multiplicity E = 1 := by
  rw [assemble unique_sector, radial_simple]

/-- The conclusion of the appendix lemma, with the standard analytic
interfaces and the two radial ground-state simplicity results explicit. -/
theorem lowest_two_planar_levels {eigen : ℤ → ℝ → Prop}
    {spectrum : Set ℝ} {lam Λ : ℝ}
    (h : RadialOrderingData eigen lam) (hs : DiscreteSpectralAssembly eigen spectrum Λ)
    (hlamΛ : lam < Λ)
    (multiplicity : ℝ → ℕ) (sectorMultiplicity : ℤ → ℝ → ℕ)
    (assemble : ∀ E m, (∀ n, eigen n E → n = m) →
      multiplicity E = sectorMultiplicity m E)
    (simple_zero : sectorMultiplicity 0 0 = 1)
    (simple_minus_one : sectorMultiplicity (-1) lam = 1) :
    (∀ E, E ∈ spectrum ∧ E ≤ lam ↔ E = 0 ∨ E = lam) ∧
      multiplicity 0 = 1 ∧ multiplicity lam = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ E, lam < E → E < lam + ε → E ∉ spectrum := by
  refine ⟨planar_spectrum_below_second h hs hlamΛ, ?_, ?_,
    planar_strict_gap h hs hlamΛ⟩
  · rw [assemble 0 0 (fun _ he => unique_sector_at_zero h he), simple_zero]
  · rw [assemble lam (-1) (fun _ he => unique_sector_at_lambda h he), simple_minus_one]

/-- A regular radial function can be cut off at a point at arbitrarily
small Dirichlet cost in two dimensions. The logarithmic cutoff has energy
`1 / log(R/ε)`. This sequence gives the elementary limiting estimate. -/
theorem logarithmic_cutoff_cost_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ 0 < 1 / L ∧ 1 / L < δ := by
  refine ⟨2 / δ, div_pos (by norm_num) hδ,
    one_div_pos.mpr (div_pos (by norm_num) hδ), ?_⟩
  have h : 1 / (2 / δ) = δ / 2 := by field_simp
  rw [h]
  linarith

/-- The logarithmic cutoff on its transition annulus. -/
def logarithmicCutoffInterior (ε R r : ℝ) : ℝ :=
  Real.log (r / ε) / Real.log (R / ε)

theorem logarithmic_cutoff_derivative (ε R r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    HasDerivAt (logarithmicCutoffInterior ε R)
      (1 / (r * Real.log (R / ε))) r := by
  have hd := ((hasDerivAt_id r).div_const ε).log
    (ne_of_gt (div_pos hr hε))
  have hd' := hd.div_const (Real.log (R / ε))
  simp only [id_eq] at hd'
  convert hd' using 1 <;> try rfl
  field_simp

/-- The complete Dirichlet cost of the logarithmic transition annulus.
Outside it the cutoff is constant, so its derivative contributes zero. -/
theorem logarithmic_cutoff_energy (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ r in ε..R, (1 / (r * Real.log (R / ε))) ^ 2 * r) =
      1 / Real.log (R / ε) := by
  have hR : 0 < R := lt_trans hε hεR
  have hlog : 0 < Real.log (R / ε) :=
    Real.log_pos ((one_lt_div hε).mpr hεR)
  calc
    (∫ r in ε..R, (1 / (r * Real.log (R / ε))) ^ 2 * r) =
        ∫ r in ε..R, (1 / r) / Real.log (R / ε) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le (le_of_lt hεR)] at hr
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hε hr.1)
      field_simp
    _ = (∫ r in ε..R, 1 / r) / Real.log (R / ε) ^ 2 := by
      rw [intervalIntegral.integral_div]
    _ = Real.log (R / ε) / Real.log (R / ε) ^ 2 := by
      rw [integral_one_div_of_pos hε hR]
    _ = 1 / Real.log (R / ε) := by field_simp

theorem logarithmic_cutoff_energy_arbitrarily_small (R δ : ℝ)
    (hR : 0 < R) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < R ∧
      (∫ r in ε..R, (1 / (r * Real.log (R / ε))) ^ 2 * r) < δ := by
  obtain ⟨L, hL, _, hLδ⟩ := logarithmic_cutoff_cost_small δ hδ
  let ε := R / Real.exp L
  have hε : 0 < ε := div_pos hR (Real.exp_pos L)
  have hεR : ε < R := div_lt_self hR (Real.one_lt_exp_iff.mpr hL)
  refine ⟨ε, hε, hεR, ?_⟩
  rw [logarithmic_cutoff_energy ε R hε hεR]
  have hdiv : R / ε = Real.exp L := by dsimp [ε]; field_simp
  rw [hdiv, Real.log_exp]
  exact hLδ

/-- The forbidden logarithmic eigenfunction branch has unbounded kinetic
energy toward the origin, as does the forbidden `1/r` branch in radial L².
Both integrands are `1/r`. -/
theorem singular_branch_energy_arbitrarily_large (R M : ℝ) (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ε < R ∧ M < ∫ r in ε..R, 1 / r := by
  let L : ℝ := max M 0 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hML : M < L := by dsimp [L]; linarith [le_max_left M 0]
  refine ⟨R / Real.exp L, div_pos hR (Real.exp_pos L), ?_, ?_⟩
  · exact (div_lt_self hR) (Real.one_lt_exp_iff.mpr hL)
  · rw [integral_one_div_of_pos (div_pos hR (Real.exp_pos L)) hR]
    have hdiv : R / (R / Real.exp L) = Real.exp L := by field_simp
    rw [hdiv, Real.log_exp]
    exact hML

/-- Uniqueness of the self-adjoint realization identifies domains as well
as actions once both realizations extend the same core operator. This
abstract consequence is used for `DD*` at the two limit-point endpoints. -/
theorem realization_from_uniqueness {Realization : Type*}
    (extendsCore selfAdjoint : Realization → Prop)
    (uniqueness : ∀ A B, extendsCore A → extendsCore B →
      selfAdjoint A → selfAdjoint B → A = B)
    (A B : Realization) (hAc : extendsCore A) (hBc : extendsCore B)
    (hAs : selfAdjoint A) (hBs : selfAdjoint B) : A = B :=
  uniqueness A B hAc hBc hAs hBs

end MagHK.Ordering
