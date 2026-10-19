import MagHK.CurrentCompletion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The passive-spin remark on the actual spin-counting L² spaces. The
spin-independent direct sum, finite exterior filling, and finite-rank Slater
reduction are uniform operator-theory inputs. All four chosen spin orbitals
and their spatial density/current sums are calculated here. -/
noncomputable section
namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open MagHK.Ordering
open scoped ComplexConjugate ContDiff BigOperators Topology
set_option maxHeartbeats 1500000
set_option simprocs false

abbrev Space := MagHK.TensorRealization.Space
abbrev Spin := Fin 2
abbrev Position := Space × Spin

def spinMeasure : Measure Position := volume.prod Measure.count
instance : SigmaFinite spinMeasure := by
  unfold spinMeasure
  infer_instance

abbrev Configuration (N : ℕ) := Fin N → Position

def configurationMeasure (N : ℕ) : Measure (Configuration N) :=
  Measure.pi fun _ => spinMeasure

abbrev FullState (N : ℕ) := Lp ℂ 2 (configurationMeasure N)

def permute (N : ℕ) (σ : Equiv.Perm (Fin N)) : Configuration N → Configuration N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N => Position) σ

theorem permute_measure (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permute N σ) (configurationMeasure N) (configurationMeasure N) :=
  measurePreserving_piCongrLeft (fun _ => spinMeasure) σ

def permutation (N : ℕ) (σ : Equiv.Perm (Fin N)) : FullState N →ₗᵢ[ℂ] FullState N :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute N σ) (permute_measure N σ)

def signScalar (N : ℕ) (σ : Equiv.Perm (Fin N)) : ℂ := (Equiv.Perm.sign σ : ℤ)

def fermionSubspace (N : ℕ) : Submodule ℂ (FullState N) where
  carrier := {ψ | ∀ σ, permutation N σ ψ = signScalar N σ • ψ}
  zero_mem' := by simp
  add_mem' := by
    intro ψ φ hψ hφ σ
    rw [map_add, hψ σ, hφ σ, smul_add]
  smul_mem' := by
    intro c ψ hψ σ
    rw [map_smul, hψ σ, smul_comm]

abbrev State (N : ℕ) := fermionSubspace N
abbrev System (N : ℕ) := DomainOperator (State N)

def Core (N : ℕ) (f : Configuration N → ℂ) : Prop :=
  (∀ s : Fin N → Spin, ContDiff ℝ ∞ (fun x : Fin N → Space => f (fun i => (x i, s i)))) ∧
  (∀ s : Fin N → Spin, HasCompactSupport (fun x : Fin N → Space => f (fun i => (x i, s i)))) ∧
  ∀ σ q, f (permute N σ q) = signScalar N σ * f q

def differentialExpression (N : ℕ) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (f : Configuration N → ℂ) (q : Configuration N) : ℂ :=
  ∑ i, MagHK.TensorRealization.differentialExpression A V W
    (fun x => f (Function.update q i (x, (q i).2))) (q i).1

structure Facts (N : ℕ) (H : System N) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) : Prop where
  selfadjoint : MagHK.OperatorModel.SelfAdjoint H
  test_action : ∀ f, Core N f → ∃ ψ : State N,
    (∀ᵐ q ∂configurationMeasure N, (ψ : FullState N) q = f q) ∧
    ∃ hψ : ψ ∈ H.domain, ∀ᵐ q ∂configurationMeasure N,
      ((H.map ⟨ψ, hψ⟩ : State N) : FullState N) q = differentialExpression N A V W f q
  weak_equation : ∀ ψ (hψ : ψ ∈ H.domain) f, Core N f →
    (∫ q, conj (f q) * ((H.map ⟨ψ, hψ⟩ : State N) : FullState N) q ∂configurationMeasure N) =
      ∫ q, conj (differentialExpression N A V W f q) * (ψ : FullState N) q ∂configurationMeasure N

def EigenFunction (N : ℕ) (H : System N) (E : ℝ) (f : Configuration N → ℂ) : Prop :=
  ∃ ψ : State N, (∀ᵐ q ∂configurationMeasure N, (ψ : FullState N) q = f q) ∧
    MagHK.OperatorModel.Eigen H E ψ

def GroundState (N : ℕ) (H : System N) (E : ℝ) (f : Configuration N → ℂ) : Prop :=
  EigenFunction N H E f ∧ (∀ e ∈ MagHK.OperatorModel.spectrum H, E ≤ e) ∧
    MagHK.OperatorModel.multiplicity H E = 1 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ MagHK.OperatorModel.spectrum H, |e - E| < δ → e = E

def spinLift (f : Space → ℂ) (s : Spin) (q : Position) : ℂ :=
  if q.2 = s then f q.1 else 0

def orbitals (f g : Space → ℂ) : Fin 4 → Position → ℂ :=
  ![spinLift f 0, spinLift f 1, spinLift g 0, spinLift g 1]

def energies (e₀ e₁ : ℝ) : Fin 4 → ℝ := ![e₀, e₀, e₁, e₁]

def OrthonormalFamily (N : ℕ) (φ : Fin N → Position → ℂ) : Prop :=
  ∀ i j, Integrable (fun q => conj (φ i q) * φ j q) spinMeasure ∧
    (∫ q, conj (φ i q) * φ j q ∂spinMeasure) = if i = j then 1 else 0

def determinant (N : ℕ) (φ : Fin N → Position → ℂ) (q : Configuration N) : ℂ :=
  (Real.sqrt (N.factorial : ℝ) : ℂ)⁻¹ * Matrix.det (fun i j => φ i (q j))

def density (N : ℕ) (ψ : Configuration (N + 1) → ℂ) (x : Space) : ℝ :=
  ∑ s : Spin, (N + 1 : ℝ) * ∫ y, Complex.normSq (ψ (Fin.cons (x, s) y)) ∂configurationMeasure N

def current (N : ℕ) (A : ℝ × ℝ → ℝ × ℝ)
    (ψ : Configuration (N + 1) → ℂ) (x d : Space) : ℝ :=
  (∑ s : Spin, (N + 1 : ℝ) * ∫ y,
    (conj (ψ (Fin.cons (x, s) y)) * fderiv ℝ (fun z => ψ (Fin.cons (z, s) y)) x d).im
      ∂configurationMeasure N) + density N ψ x * MagHK.CounterexamplePair.fieldPairing A x d

/-- Uniform spin-independent direct sums, on actual spin-labelled L², with
literal differential action and the standard doubled spectral multiplicities. -/
structure StandardSpinLibrary : Prop where
  direct_sum : ∀ (T : MagHK.TensorRealization.System) A V W,
    MagHK.FermionRealization.OneBodyRealization T A V W →
    ∃ S : System 1, Facts 1 S A V W ∧
      MagHK.OperatorModel.spectrum S = MagHK.OperatorModel.spectrum T ∧
      (∀ E, MagHK.OperatorModel.multiplicity S E = 2 * MagHK.OperatorModel.multiplicity T E) ∧
      ∀ E f, MagHK.TensorRealization.EigenFunction T E f → ∀ s,
        EigenFunction 1 S E (fun q => spinLift f s (q 0))

/-- General finite exterior filling, with all occupied shell multiplicities
accounted for. No selected energy, spin family or potential is an input field. -/
structure StandardExteriorLibrary : Prop where
  filling : ∀ N, 0 < N → ∀ (S : System 1) A V W, Facts 1 S A V W →
    ∀ (φ : Fin N → Position → ℂ) (ε : Fin N → ℝ) (cut : ℝ),
    OrthonormalFamily N φ → (∀ i, ε i ≤ cut) →
    (∀ E, E ∈ MagHK.OperatorModel.spectrum S ∧ E ≤ cut ↔ E ∈ Set.range ε) →
    (∀ E ∈ Set.range ε, MagHK.OperatorModel.multiplicity S E =
      (Finset.univ.filter (fun i => ε i = E)).card) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ E, cut < E → E < cut + δ → E ∉ MagHK.OperatorModel.spectrum S) →
    (∀ i, EigenFunction 1 S (ε i) (fun q => φ i (q 0))) →
    ∃ H : System N, Facts N H A V W ∧ GroundState N H (∑ i, ε i) (determinant N φ) ∧
      ∀ (χ : Fin N → Position → ℂ) (levels : Fin N → ℝ), OrthonormalFamily N χ →
        (∀ i, EigenFunction 1 S (levels i) (fun q => χ i (q 0))) →
        EigenFunction N H (∑ i, levels i) (determinant N χ)

/-- Standard finite-rank Slater one-body reduction. Its statement uses the
literal determinant and actual spin-summed marginal integrals for every rank,
orbital family and vector potential. -/
structure StandardSlaterReductionLibrary : Prop where
  slices : ∀ N (φ : Fin (N + 1) → Position → ℂ), OrthonormalFamily (N + 1) φ →
    (∀ i s, Differentiable ℝ (fun x => φ i (x, s))) → ∀ x s,
      Integrable (fun y => Complex.normSq (determinant (N + 1) φ (Fin.cons (x, s) y)))
        (configurationMeasure N) ∧ ∀ d,
      Integrable (fun y => (conj (determinant (N + 1) φ (Fin.cons (x, s) y)) *
        fderiv ℝ (fun z => determinant (N + 1) φ (Fin.cons (z, s) y)) x d).im)
        (configurationMeasure N)
  reduction : ∀ N (φ : Fin (N + 1) → Position → ℂ), OrthonormalFamily (N + 1) φ →
    (∀ i s, Differentiable ℝ (fun x => φ i (x, s))) →
    Integrable (fun q => Complex.normSq (determinant (N + 1) φ q)) (configurationMeasure (N + 1)) ∧
    (∫ q, Complex.normSq (determinant (N + 1) φ q) ∂configurationMeasure (N + 1)) = 1 ∧
    (∀ x, density N (determinant (N + 1) φ) x =
      ∑ s : Spin, ∑ i, Complex.normSq (φ i (x, s))) ∧
    (∀ A x d, current N A (determinant (N + 1) φ) x d =
      ∑ s : Spin, ∑ i,
        ((conj (φ i (x, s)) * fderiv ℝ (fun z => φ i (z, s)) x d).im +
          Complex.normSq (φ i (x, s)) * MagHK.CounterexamplePair.fieldPairing A x d))

private theorem spinPair_integrable (f g : Space → ℂ) (a b : Spin)
    (h : Integrable (fun x => conj (f x) * g x)) :
    Integrable (fun q => conj (spinLift f a q) * spinLift g b q) spinMeasure := by
  have he : (fun q : Position => conj (spinLift f a q) * spinLift g b q) =
      fun q => (conj (f q.1) * g q.1) * (if q.2 = a ∧ q.2 = b then (1 : ℂ) else 0) := by
    funext q
    unfold spinLift
    by_cases ha : q.2 = a
    · rw [ite_eq_left ha]
      by_cases hb : q.2 = b
      · rw [ite_eq_left hb, ite_eq_left ⟨ha, hb⟩, mul_one]
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb h.2), mul_zero, mul_zero]
    · rw [ite_eq_right ha, map_zero, zero_mul, ite_eq_right (fun h => ha h.1), mul_zero]
  rw [he]
  unfold spinMeasure
  apply h.mul_prod (ν := (Measure.count : Measure Spin)) (g := fun s : Spin => if s = a ∧ s = b then (1 : ℂ) else 0)
  have hi := (integrable_const (μ := (Measure.count : Measure Spin)) (1 : ℂ)).indicator
    ((Set.toFinite {s : Spin | s = a ∧ s = b}).measurableSet)
  have heq : ({s : Spin | s = a ∧ s = b}.indicator (fun _ => (1 : ℂ))) =
      (fun s : Spin => if s = a ∧ s = b then (1 : ℂ) else 0) := by
    funext s
    exact Set.indicator_apply {u : Spin | u = a ∧ u = b} (fun _ : Spin => (1 : ℂ)) s
  rw [← heq]
  exact hi

private theorem spinPair_integral (f g : Space → ℂ) (a b : Spin) :
    (∫ q, conj (spinLift f a q) * spinLift g b q ∂spinMeasure) =
      (∫ x, conj (f x) * g x) * if a = b then 1 else 0 := by
  have he : (fun q : Position => conj (spinLift f a q) * spinLift g b q) =
      fun q => (conj (f q.1) * g q.1) * (if q.2 = a ∧ q.2 = b then (1 : ℂ) else 0) := by
    funext q
    unfold spinLift
    by_cases ha : q.2 = a
    · rw [ite_eq_left ha]
      by_cases hb : q.2 = b
      · rw [ite_eq_left hb, ite_eq_left ⟨ha, hb⟩, mul_one]
      · rw [ite_eq_right hb, ite_eq_right (fun h => hb h.2), mul_zero, mul_zero]
    · rw [ite_eq_right ha, map_zero, zero_mul, ite_eq_right (fun h => ha h.1), mul_zero]
  rw [he, spinMeasure, integral_prod_mul (fun x : Space => conj (f x) * g x)
    (fun s : Spin => if s = a ∧ s = b then (1 : ℂ) else 0)]
  congr 1
  fin_cases a <;> fin_cases b <;> simp [integral_count]

theorem orbitals_orthonormal (f g : Space → ℂ) (h : MagHK.Slater.OrthonormalPair volume f g) :
    OrthonormalFamily 4 (orbitals f g) := by
  have hff : (∫ x, conj (f x) * f x) = 1 := by simpa only [Complex.star_def] using h.norm_f
  have hgg : (∫ x, conj (g x) * g x) = 1 := by simpa only [Complex.star_def] using h.norm_g
  have hfg : (∫ x, conj (f x) * g x) = 0 := by simpa only [Complex.star_def] using h.orthogonal_fg
  have hgf : (∫ x, conj (g x) * f x) = 0 := by simpa only [Complex.star_def] using h.orthogonal_gf
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [orbitals, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals constructor
  all_goals first
    | exact spinPair_integrable _ _ _ _ h.integrable_ff
    | exact spinPair_integrable _ _ _ _ h.integrable_gg
    | exact spinPair_integrable _ _ _ _ h.integrable_fg
    | exact spinPair_integrable _ _ _ _ h.integrable_gf
    | rw [spinPair_integral]; norm_num [hff, hgg, hfg, hgf]

theorem spinLift_differentiable (f : Space → ℂ) (hf : Differentiable ℝ f) (a s : Spin) :
    Differentiable ℝ (fun x => spinLift f a (x, s)) := by
  by_cases hs : s = a
  · simpa [spinLift, hs] using hf
  · simp only [spinLift, hs]
    exact differentiable_const 0

theorem orbitals_differentiable (f g : Space → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    ∀ i s, Differentiable ℝ (fun x => orbitals f g i (x, s)) := by
  intro i s
  fin_cases i
  all_goals first | exact spinLift_differentiable f hf _ s | exact spinLift_differentiable g hg _ s

theorem spin_density_sum (f g : Space → ℂ) (x : Space) :
    (∑ s : Spin, ∑ i : Fin 4, Complex.normSq (orbitals f g i (x, s))) =
      2 * (Complex.normSq (f x) + Complex.normSq (g x)) := by
  simp [Fin.sum_univ_succ, orbitals, spinLift]
  ring

theorem spin_current_sum (f g : Space → ℂ) (A : ℝ × ℝ → ℝ × ℝ) (x d : Space) :
    (∑ s : Spin, ∑ i : Fin 4,
      ((conj (orbitals f g i (x, s)) * fderiv ℝ (fun z => orbitals f g i (z, s)) x d).im +
        Complex.normSq (orbitals f g i (x, s)) * MagHK.CounterexamplePair.fieldPairing A x d)) =
      2 * ((conj (f x) * fderiv ℝ f x d).im + (conj (g x) * fderiv ℝ g x d).im +
        (Complex.normSq (f x) + Complex.normSq (g x)) * MagHK.CounterexamplePair.fieldPairing A x d) := by
  simp [Fin.sum_univ_succ, orbitals, spinLift]
  ring

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open MagHK.Ordering
open scoped ComplexConjugate ContDiff BigOperators Topology
theorem signScalar_conjugate (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    conj (signScalar N σ) = signScalar N σ := by simp [signScalar]

def fullConjugation (N : ℕ) : FullState N →L[ℝ] FullState N :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (configurationMeasure N)

theorem fullConjugation_ae (N : ℕ) (ψ : FullState N) :
    ∀ᵐ x ∂configurationMeasure N, fullConjugation N ψ x = conj (ψ x) := by
  simpa only [fullConjugation, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using!
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL (p := 2) ψ

theorem fullConjugation_involutive (N : ℕ) (ψ : FullState N) :
    fullConjugation N (fullConjugation N ψ) = ψ := by
  apply Lp.ext
  filter_upwards [fullConjugation_ae N (fullConjugation N ψ), fullConjugation_ae N ψ]
    with x hx hy
  rw [hx, hy, Complex.conj_conj]

theorem fullConjugation_norm (N : ℕ) (ψ : FullState N) :
    ‖fullConjugation N ψ‖ = ‖ψ‖ := by
  have h (φ : FullState N) : ‖fullConjugation N φ‖ ≤ ‖φ‖ := by
    simpa only [Complex.conjCLE_norm, one_mul] using!
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).norm_compLp_le φ
  exact le_antisymm (h ψ) (by simpa only [fullConjugation_involutive] using h (fullConjugation N ψ))

theorem fullConjugation_smul (N : ℕ) (c : ℂ) (ψ : FullState N) :
    fullConjugation N (c • ψ) = conj c • fullConjugation N ψ := by
  apply Lp.ext
  filter_upwards [fullConjugation_ae N (c • ψ), fullConjugation_ae N ψ,
    Lp.coeFn_smul c ψ, Lp.coeFn_smul (conj c) (fullConjugation N ψ)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₄]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, h₂]

theorem fullConjugation_permutation (N : ℕ) (σ : Equiv.Perm (Fin N)) (ψ : FullState N) :
    fullConjugation N (permutation N σ ψ) = permutation N σ (fullConjugation N ψ) := by
  apply Lp.ext
  have hp (φ : FullState N) : ∀ᵐ x ∂configurationMeasure N, permutation N σ φ x = φ (permute N σ x) :=
    Lp.coeFn_compMeasurePreserving φ (permute_measure N σ)
  have hk := (permute_measure N σ).quasiMeasurePreserving.ae (fullConjugation_ae N ψ)
  filter_upwards [fullConjugation_ae N (permutation N σ ψ), hp ψ,
    hp (fullConjugation N ψ), hk] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem fullConjugation_preserves (N : ℕ) (ψ : FullState N) (hψ : ψ ∈ fermionSubspace N) :
    fullConjugation N ψ ∈ fermionSubspace N := by
  intro σ
  rw [← fullConjugation_permutation, hψ σ, fullConjugation_smul, signScalar_conjugate]

def conjugation (N : ℕ) : State N ≃ₗᵢ[ℝ] State N where
  toFun ψ := ⟨fullConjugation N ψ, fullConjugation_preserves N ψ ψ.property⟩
  invFun ψ := ⟨fullConjugation N ψ, fullConjugation_preserves N ψ ψ.property⟩
  left_inv ψ := Subtype.ext (fullConjugation_involutive N ψ)
  right_inv ψ := Subtype.ext (fullConjugation_involutive N ψ)
  map_add' ψ φ := Subtype.ext (map_add (fullConjugation N) (ψ : FullState N) (φ : FullState N))
  map_smul' c ψ := Subtype.ext (map_smul (fullConjugation N) c (ψ : FullState N))
  norm_map' ψ := fullConjugation_norm N ψ

theorem conjugation_ae (N : ℕ) (ψ : State N) :
    ∀ᵐ x ∂configurationMeasure N, (conjugation N ψ : FullState N) x = conj ((ψ : FullState N) x) :=
  fullConjugation_ae N ψ

@[simp] theorem conjugation_involutive (N : ℕ) (ψ : State N) :
    conjugation N (conjugation N ψ) = ψ := Subtype.ext (fullConjugation_involutive N ψ)

def reverseOperator (N : ℕ) (H : System N) : System N where
  domain := H.domain.comap (conjugation N).toLinearEquiv.toLinearMap
  map :=
    { toFun := fun ψ => conjugation N (H.map ⟨conjugation N ψ, ψ.property⟩)
      map_add' := by
        intro ψ φ
        simp only [Submodule.coe_add, map_add]
        change conjugation N (H.map (⟨conjugation N ψ, ψ.property⟩ +
          ⟨conjugation N φ, φ.property⟩)) = _
        rw [map_add, map_add]
      map_smul' := by
        intro c ψ
        simp only [Submodule.coe_smul, map_smul]
        change conjugation N (H.map (c • ⟨conjugation N ψ, ψ.property⟩)) = _
        rw [map_smul, map_smul]
        rfl }

theorem reverse_domain (N : ℕ) (H : System N) (ψ : State N) :
    conjugation N ψ ∈ (reverseOperator N H).domain ↔ ψ ∈ H.domain := by
  change conjugation N (conjugation N ψ) ∈ H.domain ↔ _
  simp only [conjugation_involutive]

theorem reverse_action (N : ℕ) (H : System N) (ψ : State N) (hψ : ψ ∈ H.domain) :
    (reverseOperator N H).map ⟨conjugation N ψ, (reverse_domain N H ψ).mpr hψ⟩ =
      conjugation N (H.map ⟨ψ, hψ⟩) := by
  change conjugation N (H.map ⟨conjugation N (conjugation N ψ), _⟩) = _
  simp only [conjugation_involutive]

theorem reverse_eigen (N : ℕ) (H : System N) (E : ℝ) (ψ : State N)
    (hψ : OperatorModel.Eigen H E ψ) :
    OperatorModel.Eigen (reverseOperator N H) E (conjugation N ψ) := by
  obtain ⟨hd, hn, he⟩ := hψ
  refine ⟨(reverse_domain N H ψ).mpr hd, ?_, ?_⟩
  · exact fun hz => hn ((conjugation N).injective (by simpa only [map_zero] using hz))
  · rw [reverse_action N H ψ hd, he, map_smul]


/-- Universal antiunitary transport on the literal spin-labelled exterior
spaces. The reversed operator below has the inverse-image conjugate domain. -/
structure StandardSpinReversalLibrary : Prop where
  facts : ∀ N (H : System N) A V W, Facts N H A V W →
    Facts N (reverseOperator N H) (-A) V W
  spectrum : ∀ N (H : System N), MagHK.OperatorModel.SelfAdjoint H →
    MagHK.OperatorModel.spectrum (reverseOperator N H) = MagHK.OperatorModel.spectrum H
  multiplicity : ∀ N (H : System N), MagHK.OperatorModel.SelfAdjoint H → ∀ E,
    MagHK.OperatorModel.multiplicity (reverseOperator N H) E = MagHK.OperatorModel.multiplicity H E

theorem reverse_ground (library : StandardSpinReversalLibrary) (N : ℕ) (H : System N)
    (hH : MagHK.OperatorModel.SelfAdjoint H) (E : ℝ) (f : Configuration N → ℂ)
    (h : GroundState N H E f) :
    GroundState N (reverseOperator N H) E (fun q => conj (f q)) := by
  obtain ⟨⟨ψ, hψ, he⟩, hb, hm, hg⟩ := h
  refine ⟨⟨conjugation N ψ, ?_, reverse_eigen N H E ψ he⟩, ?_, ?_, ?_⟩
  · filter_upwards [conjugation_ae N ψ, hψ] with q hq hf
    rw [hq, hf]
  · simpa only [library.spectrum N H hH] using hb
  · simpa only [library.multiplicity N H hH E] using hm
  · simpa only [library.spectrum N H hH] using hg

theorem density_conjugate (N : ℕ) (ψ : Configuration (N + 1) → ℂ) (x : Space) :
    density N (fun q => conj (ψ q)) x = density N ψ x := by simp [density]

theorem current_conjugate (N : ℕ) (A : ℝ × ℝ → ℝ × ℝ)
    (ψ : Configuration (N + 1) → ℂ) (x d : Space) :
    current N (-A) (fun q => conj (ψ q)) x d = -current N A ψ x d := by
  have he (s : Spin) (y : Configuration N) :
      (conj (conj (ψ (Fin.cons (x, s) y))) *
        fderiv ℝ (fun z => conj (ψ (Fin.cons (z, s) y))) x d).im =
      -(conj (ψ (Fin.cons (x, s) y)) *
        fderiv ℝ (fun z => ψ (Fin.cons (z, s) y)) x d).im := by
    rw [MagHK.OperatorTimeReversal.fderiv_conjugate, Complex.conj_conj]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  unfold current
  simp_rw [he, integral_neg]
  rw [density_conjugate]
  simp only [MagHK.CounterexamplePair.fieldPairing, Pi.neg_apply, Prod.fst_neg,
    Prod.snd_neg, neg_mul, neg_add, mul_neg, Finset.sum_neg_distrib]
  ring

/-- All first-two-level inputs are retained on the same actual spatial
operator and the same actual orbitals. -/
structure SpatialData (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (e₀ e₁ : ℝ) (f g : Space → ℂ) where
  operator : MagHK.TensorRealization.System
  facts : MagHK.FermionRealization.OneBodyRealization operator A V W
  ordered : e₀ < e₁
  levels : ∀ E, E ∈ MagHK.OperatorModel.spectrum operator ∧ E ≤ e₁ ↔ E = e₀ ∨ E = e₁
  first_simple : MagHK.OperatorModel.multiplicity operator e₀ = 1
  second_simple : MagHK.OperatorModel.multiplicity operator e₁ = 1
  gap : ∃ δ : ℝ, 0 < δ ∧ ∀ E, e₁ < E → E < e₁ + δ → E ∉ MagHK.OperatorModel.spectrum operator
  first_eigen : MagHK.TensorRealization.EigenFunction operator e₀ f
  second_eigen : MagHK.TensorRealization.EigenFunction operator e₁ g
  orthonormal : MagHK.Slater.OrthonormalPair volume f g

private theorem range_energies (e₀ e₁ E : ℝ) :
    E ∈ Set.range (energies e₀ e₁) ↔ E = e₀ ∨ E = e₁ := by
  simp [energies, eq_comm, or_comm]

private theorem occupation_count (e₀ e₁ : ℝ) (h : e₀ < e₁) (E : ℝ)
    (hE : E = e₀ ∨ E = e₁) :
    (Finset.univ.filter (fun i : Fin 4 => energies e₀ e₁ i = E)).card = 2 := by
  rcases hE with rfl | rfl
  · have he : Finset.univ.filter (fun i : Fin 4 => energies E e₁ i = E) = {0, 1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      fin_cases i <;> dsimp [energies]
      all_goals simp [ne_of_gt h]
    rw [he]
    decide
  · have he : Finset.univ.filter (fun i : Fin 4 => energies e₀ E i = E) = {2, 3} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      fin_cases i <;> dsimp [energies]
      all_goals simp [ne_of_lt h]
    rw [he]
    decide

structure FilledResult (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (e₀ e₁ : ℝ) (f g : Space → ℂ) where
  one_body : System 1
  one_facts : Facts 1 one_body A V W
  first_double : MagHK.OperatorModel.multiplicity one_body e₀ = 2
  second_double : MagHK.OperatorModel.multiplicity one_body e₁ = 2
  occupied : ∀ i, EigenFunction 1 one_body (energies e₀ e₁ i)
    (fun q => orbitals f g i (q 0))
  operator : System 4
  facts : Facts 4 operator A V W
  ground : GroundState 4 operator (2 * (e₀ + e₁)) (determinant 4 (orbitals f g))
  norm_integrable : Integrable (fun q => Complex.normSq (determinant 4 (orbitals f g) q))
    (configurationMeasure 4)
  slices_integrable : ∀ x s,
    Integrable (fun y => Complex.normSq (determinant 4 (orbitals f g) (Fin.cons (x, s) y)))
      (configurationMeasure 3) ∧ ∀ d,
    Integrable (fun y => (conj (determinant 4 (orbitals f g) (Fin.cons (x, s) y)) *
      fderiv ℝ (fun z => determinant 4 (orbitals f g) (Fin.cons (z, s) y)) x d).im)
      (configurationMeasure 3)
  normalized : (∫ q, Complex.normSq (determinant 4 (orbitals f g) q) ∂configurationMeasure 4) = 1
  density_formula : ∀ x, density 3 (determinant 4 (orbitals f g)) x =
    2 * (Complex.normSq (f x) + Complex.normSq (g x))
  current_formula : ∀ x d, current 3 A (determinant 4 (orbitals f g)) x d =
    2 * ((conj (f x) * fderiv ℝ f x d).im + (conj (g x) * fderiv ℝ g x d).im +
      (Complex.normSq (f x) + Complex.normSq (g x)) * MagHK.CounterexamplePair.fieldPairing A x d)

theorem fill_doublets (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (e₀ e₁ : ℝ) (f g : Space → ℂ)
    (D : SpatialData A V W e₀ e₁ f g) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Nonempty (FilledResult A V W e₀ e₁ f g) := by
  obtain ⟨S, hS, hs, hm, hlift⟩ := spin.direct_sum D.operator A V W D.facts
  have ho := orbitals_orthonormal f g D.orthonormal
  have hlevels (E : ℝ) : E ∈ MagHK.OperatorModel.spectrum S ∧ E ≤ e₁ ↔
      E ∈ Set.range (energies e₀ e₁) := by
    rw [hs, D.levels, range_energies]
  have hcount (E : ℝ) (hE : E ∈ Set.range (energies e₀ e₁)) :
      MagHK.OperatorModel.multiplicity S E =
        (Finset.univ.filter (fun i => energies e₀ e₁ i = E)).card := by
    have he := (range_energies e₀ e₁ E).mp hE
    rw [occupation_count e₀ e₁ D.ordered E he, hm]
    rcases he with rfl | rfl
    · simp only [D.first_simple, mul_one]
    · simp only [D.second_simple, mul_one]
  have hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ E, e₁ < E → E < e₁ + δ → E ∉ MagHK.OperatorModel.spectrum S := by
    simpa only [hs] using D.gap
  have heigen (i : Fin 4) : EigenFunction 1 S (energies e₀ e₁ i)
      (fun q => orbitals f g i (q 0)) := by
    fin_cases i
    all_goals first | exact hlift _ _ D.first_eigen _ | exact hlift _ _ D.second_eigen _
  obtain ⟨H, hH, hground, _⟩ := exterior.filling 4 (by norm_num) S A V W hS
    (orbitals f g) (energies e₀ e₁) e₁ ho
    (by intro i; fin_cases i <;> first | exact D.ordered.le | exact le_rfl)
    hlevels hcount hgap heigen
  have he : (∑ i, energies e₀ e₁ i) = 2 * (e₀ + e₁) := by simp [Fin.sum_univ_succ, energies]; ring
  rw [he] at hground
  obtain ⟨hi, hn, hρ, hj⟩ := reduction.reduction 3 (orbitals f g) ho (orbitals_differentiable f g hf hg)
  refine ⟨⟨S, hS, ?_, ?_, heigen, H, hH, hground, hi,
    reduction.slices 3 _ ho (orbitals_differentiable f g hf hg), hn, ?_, ?_⟩⟩
  · simp only [hm, D.first_simple, mul_one]
  · simp only [hm, D.second_simple, mul_one]
  · intro x
    rw [hρ, spin_density_sum]
  · intro x d
    rw [hj, spin_current_sum]

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open MagHK.Ordering MagHK.TensorRealization
open scoped ComplexConjugate ContDiff BigOperators Topology

theorem bounded_spatial_data
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (c : ℝ) (hc : 0 < c) (hgap : 20 < c ^ 2) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (SpatialData (MagHK.Cartesian.boundedVector t)
      (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential c) 0 20
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) := by
  obtain ⟨t, ht, heq, _⟩ := MagHK.Noninteracting.exists_bounded_parameter
  obtain ⟨P, hP, hlevels, hp0, hp20, hpgap⟩ :=
    PlanarSpectralLibrary.bounded_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := AxialRealization.bounded_axial_realization axial c hc
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (AxialRealization.bounded_coefficients c).V_smooth hP hZ
    (spectrum_nonnegative P.spectrum hlevels) hZ.nonnegative
  have h1 : MagHK.FermionRealization.OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t)
      (Axial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm20, htg⟩ := bounded_tensor_levels T P Z _ _ _ hT c hgap
    hlevels hp0 hp20 hpgap hz0 hzm hzgap
  have hzero := bounded_zero_eigenfunction t c ht hc P Z T hP hz hT
  have hminus := bounded_minus_eigenfunction t c ht hc P Z T hP hz hT
  have ho := CartesianOrbitals.bounded_orthonormal t c ht hc heq
  exact ⟨t, ht, ⟨⟨T, h1, by norm_num, hle, hm0, hm20, htg, hzero, hminus, ho⟩⟩⟩

open MagHK.Noninteracting MagHK.GaussianIntegrals MagHK.Cartesian MagHK.GaussianFermion

theorem gaussian_spatial_data
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (SpatialData (MagHK.Cartesian.gaussianVector t)
      (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht, hn0, hn1⟩ := exists_gaussian_equal_norms
  obtain ⟨P, hP, hlevels, hp0, hp2, hpgap⟩ :=
    GaussianPlanar.gaussian_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := GaussianAxial.gaussian_axial_realization axial c hc0
  have hpnon : ∀ E ∈ P.spectrum, 0 ≤ E := by
    intro E hE
    by_cases he : E ≤ 2
    · rcases (hlevels E).mp ⟨hE, he⟩ with rfl | rfl <;> norm_num
    · linarith
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (GaussianPlanar.gaussian_planar_coefficients t ht.le) (GaussianAxial.potential_smooth c)
    hP hZ hpnon hZ.nonnegative
  have h1 : FermionRealization.OneBodyRealization T (gaussianVector t) (gaussianScalar t)
      (GaussianAxial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm2, htg⟩ := tensor_levels T P Z _ _ _ hT 2 (2 * c)
    (by norm_num) (by linarith) hlevels hp0 hp2 hpgap hz0 hzm hzgap
  have hzero := gaussian_zero_eigenfunction t c ht hc0 P Z T hP hz hT
  have hminus := gaussian_minus_eigenfunction t c ht hc0 P Z T hP hz hT
  have ho := GaussianOrbitals.gaussian_orthonormal t c ht hc0 hn0 hn1
  exact ⟨t, ht, ⟨⟨T, h1, by norm_num, hle, hm0, hm2, htg, hzero, hminus, ho⟩⟩⟩

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open scoped ComplexConjugate ContDiff BigOperators Topology

structure PairedResult (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (e₀ e₁ : ℝ) (f g : Space → ℂ) where
  filled : FilledResult A V W e₀ e₁ f g
  reversed_facts : Facts 4 (reverseOperator 4 filled.operator) (-A) V W
  reversed_ground : GroundState 4 (reverseOperator 4 filled.operator) (2 * (e₀ + e₁))
    (fun q => conj (determinant 4 (orbitals f g) q))
  reversed_normalized :
    (∫ q, Complex.normSq (conj (determinant 4 (orbitals f g) q)) ∂configurationMeasure 4) = 1
  doubled_density : ∀ x, density 3 (determinant 4 (orbitals f g)) x =
    2 * MagHK.CounterexamplePair.density (MagHK.FermionRealization.determinant f g) x
  equal_density : ∀ x, density 3 (fun q => conj (determinant 4 (orbitals f g) q)) x =
    density 3 (determinant 4 (orbitals f g)) x
  zero_currents : ∀ x d, current 3 A (determinant 4 (orbitals f g)) x d = 0 ∧
    current 3 (-A) (fun q => conj (determinant 4 (orbitals f g) q)) x d = 0

theorem paired_filling (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (e₀ e₁ : ℝ) (f g : Space → ℂ)
    (D : SpatialData A V W e₀ e₁ f g) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hj : ∀ x d, (conj (f x) * fderiv ℝ f x d).im + (conj (g x) * fderiv ℝ g x d).im +
      (Complex.normSq (f x) + Complex.normSq (g x)) * MagHK.CounterexamplePair.fieldPairing A x d = 0) :
    Nonempty (PairedResult A V W e₀ e₁ f g) := by
  obtain ⟨R⟩ := fill_doublets spin exterior reduction A V W e₀ e₁ f g D hf hg
  refine ⟨⟨R, reversal.facts 4 R.operator A V W R.facts,
    reverse_ground reversal 4 R.operator R.facts.selfadjoint _ _ R.ground,
    ?_, ?_, density_conjugate 3 _, ?_⟩⟩
  · simpa using R.normalized
  · intro x
    rw [R.density_formula]
    congr 1
    exact (MagHK.Slater.slater_density_marginal volume f g D.orthonormal (f x) (g x)).symm
  · intro x d
    have hz : current 3 A (determinant 4 (orbitals f g)) x d = 0 := by
      rw [R.current_formula, hj x d, mul_zero]
    exact ⟨hz, by rw [current_conjugate, hz, neg_zero]⟩

/-- Passive spin fills the same two bounded spatial levels, each with two
spin states. The energy is 40, the actual four-particle ground eigenspace is
one-dimensional, both signs have equal doubled density, and current is zero. -/
theorem bounded_passive_spin
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (PairedResult (MagHK.Cartesian.boundedVector t)
      (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential 5) 0 20
      (MagHK.CartesianOrbitals.orbitalZero t 5) (MagHK.CartesianOrbitals.orbitalMinus t 5)) := by
  obtain ⟨t, ht, ⟨D⟩⟩ := bounded_spatial_data planar axial tensor 5 (by norm_num) (by norm_num)
  refine ⟨t, ht, paired_filling spin exterior reduction reversal _ _ _ _ _ _ _ D
    (MagHK.CurrentCompletion.Bounded.orbitalZero_differentiable t 5 ht.le)
    (MagHK.CurrentCompletion.Bounded.orbitalMinus_differentiable t 5 ht.le) ?_⟩
  intro x d
  have h := MagHK.CurrentCompletion.Bounded.orbital_current_cancels t 5 ht.le x d
  simpa only [Complex.star_def, MagHK.ConcreteSlater.density, MagHK.ConcreteSlater.fieldPairing,
    MagHK.ConcreteSlater.realCoordinates, MagHK.ConstructionData.bounded3Vector,
    MagHK.CounterexamplePair.fieldPairing, zero_mul, add_zero] using h

/-- The confining Gaussian construction has the analogous passive-spin
four-particle ground state at energy 4, with the same literal density doubling. -/
theorem gaussian_passive_spin
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (PairedResult (MagHK.Cartesian.gaussianVector t)
      (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) := by
  obtain ⟨t, ht, ⟨D⟩⟩ := gaussian_spatial_data planar axial tensor c hc
  refine ⟨t, ht, paired_filling spin exterior reduction reversal _ _ _ _ _ _ _ D
    (MagHK.CurrentCompletion.Gaussian.orbitalZero_differentiable t c ht.le)
    (MagHK.CurrentCompletion.Gaussian.orbitalMinus_differentiable t c ht.le) ?_⟩
  intro x d
  have h := MagHK.CurrentCompletion.Gaussian.orbital_current_cancels t c ht.le x d
  simpa only [Complex.star_def, MagHK.GaussianSlater.density, MagHK.GaussianSlater.fieldPairing,
    MagHK.GaussianSlater.realCoordinates, MagHK.ConstructionData.gaussian3Vector,
    MagHK.CounterexamplePair.fieldPairing, zero_mul, add_zero] using h

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open scoped ComplexConjugate ContDiff BigOperators Topology

private theorem orthonormal_comp {N M : ℕ} (φ : Fin N → Position → ℂ)
    (hφ : OrthonormalFamily N φ) (e : Fin M → Fin N) (he : Function.Injective e) :
    OrthonormalFamily M (fun i => φ (e i)) := by
  intro i j
  obtain ⟨hi, hv⟩ := hφ (e i) (e j)
  exact ⟨hi, by simpa only [he.eq_iff] using hv⟩

def firstIndices : Fin 2 → Fin 4 := ![0, 1]
def polarizedIndices : Fin 2 → Fin 4 := ![0, 2]

def lowestDeterminant (f g : Space → ℂ) : Configuration 2 → ℂ :=
  determinant 2 (fun i => orbitals f g (firstIndices i))

def polarizedDeterminant (f g : Space → ℂ) : Configuration 2 → ℂ :=
  determinant 2 (fun i => orbitals f g (polarizedIndices i))

private theorem eigenFunction_spectrum (N : ℕ) (H : System N) (E : ℝ)
    (f : Configuration N → ℂ) (h : EigenFunction N H E f) : E ∈ MagHK.OperatorModel.spectrum H := by
  obtain ⟨ψ, _, hψ, hn, he⟩ := h
  rintro ⟨R, _, _, hR⟩
  have hz := hR ψ hψ
  rw [he, sub_self, map_zero] at hz
  exact hn hz.symm

private theorem eigenFunction_energy_unique (N : ℕ) (H : System N) (E E' : ℝ)
    (f : Configuration N → ℂ) (h : EigenFunction N H E f) (h' : EigenFunction N H E' f) : E = E' := by
  obtain ⟨ψ, hψ, hd, hn, he⟩ := h
  obtain ⟨φ, hφ, hd', _, he'⟩ := h'
  have heq : ψ = φ := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hψ, hφ] with q hq hq'
    exact hq.trans hq'.symm
  subst φ
  have hv : E • ψ = E' • ψ := he.symm.trans he'
  have hz : (E - E') • ψ = 0 := by rw [sub_smul, hv, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)

structure UnrestrictedTwoResult (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ)
    (e₀ e₁ : ℝ) (f g : Space → ℂ) where
  operator : System 2
  facts : Facts 2 operator A V W
  ground : GroundState 2 operator (2 * e₀) (lowestDeterminant f g)
  polarized_eigen : EigenFunction 2 operator (e₀ + e₁) (polarizedDeterminant f g)
  polarized_not_ground : ∀ E, ¬GroundState 2 operator E (polarizedDeterminant f g)
  normalized : (∫ q, Complex.normSq (lowestDeterminant f g q) ∂configurationMeasure 2) = 1
  density_formula : ∀ x, density 1 (lowestDeterminant f g) x = 2 * Complex.normSq (f x)

/-- With unrestricted passive spin, two particles fill the first spatial
orbital twice. The polarized determinant using the second spatial orbital is
an eigenstate of strictly higher energy and cannot be a ground state. -/
theorem fill_lowest_doublet (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (e₀ e₁ : ℝ) (f g : Space → ℂ)
    (D : SpatialData A V W e₀ e₁ f g) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Nonempty (UnrestrictedTwoResult A V W e₀ e₁ f g) := by
  obtain ⟨S, hS, hs, hm, hlift⟩ := spin.direct_sum D.operator A V W D.facts
  have ho4 := orbitals_orthonormal f g D.orthonormal
  have hi : Function.Injective firstIndices := by intro i j; fin_cases i <;> fin_cases j <;> decide
  have hp : Function.Injective polarizedIndices := by intro i j; fin_cases i <;> fin_cases j <;> decide
  have ho := orthonormal_comp _ ho4 firstIndices hi
  have hop := orthonormal_comp _ ho4 polarizedIndices hp
  have hlevels (E : ℝ) : E ∈ MagHK.OperatorModel.spectrum S ∧ E ≤ e₀ ↔
      E ∈ Set.range (fun _ : Fin 2 => e₀) := by
    simp only [Set.range_const, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hE, hle⟩
      rw [hs] at hE
      rcases (D.levels E).mp ⟨hE, hle.trans D.ordered.le⟩ with he | he
      · exact he
      · rw [he] at hle
        exact (D.ordered.not_ge hle).elim
    · intro hE
      subst E
      exact ⟨by rw [hs]; exact ((D.levels e₀).mpr (Or.inl rfl)).1, le_rfl⟩
  have hcount (E : ℝ) (hE : E ∈ Set.range (fun _ : Fin 2 => e₀)) :
      MagHK.OperatorModel.multiplicity S E =
        (Finset.univ.filter (fun _ : Fin 2 => e₀ = E)).card := by
    rcases hE with ⟨i, rfl⟩
    simp [hm, D.first_simple]
  have hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ E, e₀ < E → E < e₀ + δ → E ∉ MagHK.OperatorModel.spectrum S := by
    refine ⟨e₁ - e₀, sub_pos.mpr D.ordered, fun E hE hupper hspec => ?_⟩
    rw [hs] at hspec
    have hless : E < e₁ := by linarith
    rcases (D.levels E).mp ⟨hspec, hless.le⟩ with he | he <;> linarith
  have heigen (i : Fin 2) : EigenFunction 1 S e₀
      (fun q => orbitals f g (firstIndices i) (q 0)) := by
    fin_cases i <;> exact hlift _ _ D.first_eigen _
  obtain ⟨H, hH, hground, haction⟩ := exterior.filling 2 (by norm_num) S A V W hS
    (fun i => orbitals f g (firstIndices i)) (fun _ => e₀) e₀ ho (fun _ => le_rfl)
    hlevels hcount hgap heigen
  have heigenp (i : Fin 2) : EigenFunction 1 S (![e₀, e₁] i)
      (fun q => orbitals f g (polarizedIndices i) (q 0)) := by
    fin_cases i
    · exact hlift _ _ D.first_eigen _
    · exact hlift _ _ D.second_eigen _
  have hpol := haction (fun i => orbitals f g (polarizedIndices i)) ![e₀, e₁] hop heigenp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hground hpol
  have hground' : GroundState 2 H (2 * e₀) (lowestDeterminant f g) := by
    simpa only [lowestDeterminant, two_mul] using hground
  have hpol' : EigenFunction 2 H (e₀ + e₁) (polarizedDeterminant f g) := hpol
  have hdiff : ∀ i s, Differentiable ℝ (fun x => orbitals f g (firstIndices i) (x, s)) :=
    fun i s => orbitals_differentiable f g hf hg _ s
  obtain ⟨_, hn, hρ, _⟩ := reduction.reduction 1 _ ho hdiff
  refine ⟨⟨H, hH, hground', hpol', ?_, hn, ?_⟩⟩
  · intro E hbad
    have hE := eigenFunction_energy_unique 2 H E (e₀ + e₁) _ hbad.1 hpol'
    have hbound := hbad.2.1 (2 * e₀) (eigenFunction_spectrum 2 H _ _ hground'.1)
    linarith [D.ordered]
  · intro x
    rw [show density 1 (lowestDeterminant f g) x = _ from hρ x]
    simp [Fin.sum_univ_succ, firstIndices, orbitals, spinLift]
    ring

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin
open MeasureTheory Set Filter
open scoped ComplexConjugate ContDiff BigOperators Topology

theorem polarizedDeterminant_formula (f g : Space → ℂ) (q : Configuration 2) :
    polarizedDeterminant f g q = if (q 0).2 = 0 ∧ (q 1).2 = 0 then
      MagHK.FermionRealization.determinant f g ((q 0).1, (q 1).1) else 0 := by
  unfold polarizedDeterminant determinant
  change (Real.sqrt (Nat.factorial 2 : ℝ) : ℂ)⁻¹ *
      (Matrix.det (Matrix.of (fun i j : Fin 2 => orbitals f g (polarizedIndices i) (q j)))) = _
  rw [Matrix.det_fin_two]
  dsimp only [Matrix.of_apply, polarizedIndices, orbitals]
  by_cases h₀ : (q 0).2 = 0 <;> by_cases h₁ : (q 1).2 = 0
  all_goals simp_all [spinLift, MagHK.FermionRealization.determinant, MagHK.Slater.slaterSlice,
    MagHK.Slater.determinantSlice, MagHK.Slater.scale, Nat.factorial]
  all_goals ring

/-- Both spin remarks for the same bounded construction parameter. -/
theorem bounded_passive_spin_complete
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary) :
    ∃ t : ℝ, 0 < t ∧
      Nonempty (PairedResult (MagHK.Cartesian.boundedVector t)
        (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential 5) 0 20
        (MagHK.CartesianOrbitals.orbitalZero t 5) (MagHK.CartesianOrbitals.orbitalMinus t 5)) ∧
      Nonempty (UnrestrictedTwoResult (MagHK.Cartesian.boundedVector t)
        (MagHK.Cartesian.boundedScalar t) (MagHK.Axial.potential 5) 0 20
        (MagHK.CartesianOrbitals.orbitalZero t 5) (MagHK.CartesianOrbitals.orbitalMinus t 5)) := by
  obtain ⟨t, ht, ⟨D⟩⟩ := bounded_spatial_data planar axial tensor 5 (by norm_num) (by norm_num)
  have hf := MagHK.CurrentCompletion.Bounded.orbitalZero_differentiable t 5 ht.le
  have hg := MagHK.CurrentCompletion.Bounded.orbitalMinus_differentiable t 5 ht.le
  refine ⟨t, ht, paired_filling spin exterior reduction reversal _ _ _ _ _ _ _ D hf hg ?_,
    fill_lowest_doublet spin exterior reduction _ _ _ _ _ _ _ D hf hg⟩
  intro x d
  have h := MagHK.CurrentCompletion.Bounded.orbital_current_cancels t 5 ht.le x d
  simpa only [Complex.star_def, MagHK.ConcreteSlater.density, MagHK.ConcreteSlater.fieldPairing,
    MagHK.ConcreteSlater.realCoordinates, MagHK.ConstructionData.bounded3Vector,
    MagHK.CounterexamplePair.fieldPairing, zero_mul, add_zero] using h

/-- Both spin remarks for the same Gaussian construction parameter. -/
theorem gaussian_passive_spin_complete
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (spin : StandardSpinLibrary) (exterior : StandardExteriorLibrary)
    (reduction : StandardSlaterReductionLibrary) (reversal : StandardSpinReversalLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧
      Nonempty (PairedResult (MagHK.Cartesian.gaussianVector t)
        (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
        (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) ∧
      Nonempty (UnrestrictedTwoResult (MagHK.Cartesian.gaussianVector t)
        (MagHK.Cartesian.gaussianScalar t) (MagHK.GaussianAxial.potential c) 0 2
        (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) := by
  obtain ⟨t, ht, ⟨D⟩⟩ := gaussian_spatial_data planar axial tensor c hc
  have hf := MagHK.CurrentCompletion.Gaussian.orbitalZero_differentiable t c ht.le
  have hg := MagHK.CurrentCompletion.Gaussian.orbitalMinus_differentiable t c ht.le
  refine ⟨t, ht, paired_filling spin exterior reduction reversal _ _ _ _ _ _ _ D hf hg ?_,
    fill_lowest_doublet spin exterior reduction _ _ _ _ _ _ _ D hf hg⟩
  intro x d
  have h := MagHK.CurrentCompletion.Gaussian.orbital_current_cancels t c ht.le x d
  simpa only [Complex.star_def, MagHK.GaussianSlater.density, MagHK.GaussianSlater.fieldPairing,
    MagHK.GaussianSlater.realCoordinates, MagHK.ConstructionData.gaussian3Vector,
    MagHK.CounterexamplePair.fieldPairing, zero_mul, add_zero] using h

end MagHK.PassiveSpin

namespace MagHK.PassiveSpin

/-- The two completely occupied spin doublets contribute the exterior
multiplicity binom(2,2) times binom(2,2), equal to one. -/
theorem FilledResult.multiplicity_product
    {A : ℝ × ℝ → ℝ × ℝ} {V : ℝ × ℝ → ℝ} {W : ℝ → ℝ}
    {e₀ e₁ : ℝ} {f g : Space → ℂ} (R : FilledResult A V W e₀ e₁ f g) :
    MagHK.OperatorModel.multiplicity R.operator (2 * (e₀ + e₁)) =
      Nat.choose (MagHK.OperatorModel.multiplicity R.one_body e₀) 2 *
        Nat.choose (MagHK.OperatorModel.multiplicity R.one_body e₁) 2 := by
  rw [R.ground.2.2.1, R.first_double, R.second_double]
  norm_num

theorem bounded_density_pos (t : ℝ) (ht : 0 ≤ t)
    (R : PairedResult (MagHK.Cartesian.boundedVector t) (MagHK.Cartesian.boundedScalar t)
      (MagHK.Axial.potential 5) 0 20 (MagHK.CartesianOrbitals.orbitalZero t 5)
      (MagHK.CartesianOrbitals.orbitalMinus t 5)) (x : Space) :
    0 < density 3 (determinant 4 (orbitals (MagHK.CartesianOrbitals.orbitalZero t 5)
      (MagHK.CartesianOrbitals.orbitalMinus t 5))) x := by
  rw [R.filled.density_formula]
  exact mul_pos (by norm_num) (MagHK.ConcreteSlater.density_pos t 5 ht (by norm_num) x)

theorem gaussian_density_pos (t c : ℝ) (ht : 0 ≤ t) (hc : 0 < c)
    (R : PairedResult (MagHK.Cartesian.gaussianVector t) (MagHK.Cartesian.gaussianScalar t)
      (MagHK.GaussianAxial.potential c) 0 2 (MagHK.GaussianOrbitals.orbitalZero t c)
      (MagHK.GaussianOrbitals.orbitalMinus t c)) (x : Space) :
    0 < density 3 (determinant 4 (orbitals (MagHK.GaussianOrbitals.orbitalZero t c)
      (MagHK.GaussianOrbitals.orbitalMinus t c))) x := by
  rw [R.filled.density_formula]
  exact mul_pos (by norm_num) (MagHK.GaussianSlater.density_pos t c ht hc x)

end MagHK.PassiveSpin
