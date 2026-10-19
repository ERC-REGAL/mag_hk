import MagHK.OperatorTimeReversal
import MagHK.MonopoleRealization
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.GroupTheory.Perm.Sign

/-! General finite-particle time reversal on the actual antisymmetric L² space.
The fields and real many-body potential are arbitrary. Existence of the
semibounded Friedrichs form realization is explicit. The only external
transport results are universal antiunitary spectral theory and the
representation theorem for conjugate closed forms. No state, energy or
ground-state assertion occurs in those inputs.
-/
noncomputable section
namespace MagHK.ManyBodyTimeReversal
open MeasureTheory Set Filter
open MagHK.Ordering
open scoped ComplexConjugate ContDiff BigOperators
set_option maxHeartbeats 1000000

abbrev Point := Fin 3 → ℝ
abbrev Configuration (N : ℕ) := Fin N → Point
abbrev FullState (N : ℕ) := Lp ℂ 2 (volume : Measure (Configuration N))

def permute (N : ℕ) (σ : Equiv.Perm (Fin N)) : Configuration N → Configuration N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N => Point) σ

theorem permute_measure (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permute N σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin N => Point) σ

def permutation (N : ℕ) (σ : Equiv.Perm (Fin N)) : FullState N →ₗᵢ[ℂ] FullState N :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute N σ) (permute_measure N σ)

def signScalar (N : ℕ) (σ : Equiv.Perm (Fin N)) : ℂ := (Equiv.Perm.sign σ : ℤ)

theorem signScalar_conjugate (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    conj (signScalar N σ) = signScalar N σ := by simp [signScalar]

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

def fullConjugation (N : ℕ) : FullState N →L[ℝ] FullState N :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 volume

theorem fullConjugation_ae (N : ℕ) (ψ : FullState N) :
    ∀ᵐ x, fullConjugation N ψ x = conj (ψ x) := by
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
  have hp (φ : FullState N) : ∀ᵐ x, permutation N σ φ x = φ (permute N σ x) :=
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
    ∀ᵐ x, (conjugation N ψ : FullState N) x = conj ((ψ : FullState N) x) :=
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

def direction (N : ℕ) (i : Fin N) (k : Fin 3) : Configuration N :=
  Pi.single i (Pi.single k 1)

def momentum (N : ℕ) (A : Point → Point) (f : Configuration N → ℂ)
    (i : Fin N) (k : Fin 3) (x : Configuration N) : ℂ :=
  -Complex.I * fderiv ℝ f x (direction N i k) + (A (x i) k : ℂ) * f x

def form (N : ℕ) (A : Point → Point) (V : Configuration N → ℝ)
    (f g : Configuration N → ℂ) : ℂ :=
  ∫ x, (∑ i : Fin N, ∑ k : Fin 3,
    conj (momentum N A f i k x) * momentum N A g i k x) +
    (V x : ℂ) * conj (f x) * g x

/-- The literal external scalar potential and real pair Coulomb interaction. -/
def hamiltonianPotential (N : ℕ) (v : Point → ℝ) (κ : ℝ) (x : Configuration N) : ℝ :=
  (∑ i : Fin N, v (x i)) + κ * ∑ i : Fin N, ∑ j : Fin N,
    if i < j then (Real.sqrt (∑ k : Fin 3, (x i k - x j k) ^ 2))⁻¹ else 0

def Core (N : ℕ) (f : Configuration N → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ∀ σ x, f (permute N σ x) = signScalar N σ * f x

theorem core_conjugate (N : ℕ) (f : Configuration N → ℂ) (hf : Core N f) :
    Core N (fun x => conj (f x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hf.1, ?_, ?_⟩
  · exact hf.2.1.comp_left (by simp)
  · intro σ x
    dsimp only
    rw [hf.2.2 σ x, map_mul, signScalar_conjugate]

theorem momentum_conjugate (N : ℕ) (A : Point → Point) (f : Configuration N → ℂ)
    (i : Fin N) (k : Fin 3) (x : Configuration N) :
    momentum N (-A) (fun y => conj (f y)) i k x = -conj (momentum N A f i k x) := by
  simp only [momentum, OperatorTimeReversal.fderiv_conjugate, Pi.neg_apply,
    map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem form_conjugate (N : ℕ) (A : Point → Point) (V : Configuration N → ℝ)
    (f g : Configuration N → ℂ) :
    form N (-A) V (fun x => conj (f x)) (fun x => conj (g x)) = conj (form N A V f g) := by
  unfold form
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [momentum_conjugate, map_add, map_sum, map_mul, map_neg,
    Complex.conj_conj, Complex.conj_ofReal, neg_mul_neg]

def Facts (N : ℕ) (H : System N) (A : Point → Point) (V : Configuration N → ℝ)
    (b : ℝ) : Prop :=
  OperatorModel.SelfAdjoint H ∧
  (∀ f g, Core N f → Core N g → Integrable (fun x =>
    (∑ i : Fin N, ∑ k : Fin 3, conj (momentum N A f i k x) * momentum N A g i k x) +
      ((V x + b : ℝ) : ℂ) * conj (f x) * g x)) ∧
  (∀ f, Core N f → 0 ≤ (form N A (fun x => V x + b) f f).re) ∧
  ∀ ψ η, (∃ hψ : ψ ∈ H.domain, H.map ⟨ψ, hψ⟩ = η) ↔
    MonopoleRealization.FriedrichsGraph volume (Core N)
      (fun f g => form N A (fun x => V x + b) f g)
      (ψ : FullState N) ((η + b • ψ : State N) : FullState N)

/-- The general representation theorem transports a Friedrichs graph under
an antiunitary that preserves the core and conjugates its sesquilinear form.
The covariance identities are premises and are discharged above. The shift
b allows arbitrary semibounded real scalar potentials. -/
def StandardClosedFormLibrary : Prop :=
  ∀ N (H : System N) A V b, Facts N H A V b →
    (∀ f, Core N f → Core N (fun x => conj (f x))) →
    (∀ f g, form N (-A) (fun x => V x + b) (fun x => conj (f x)) (fun x => conj (g x)) =
      conj (form N A (fun x => V x + b) f g)) →
    Facts N (reverseOperator N H) (-A) V b

def StandardAntiunitaryLibrary : Prop :=
  ∀ N (H : System N), OperatorModel.SelfAdjoint H →
    OperatorModel.spectrum (reverseOperator N H) = OperatorModel.spectrum H ∧
    OperatorModel.multiplicity (reverseOperator N H) = OperatorModel.multiplicity H

def GroundState (N : ℕ) (H : System N) (E : ℝ) (ψ : State N) : Prop :=
  OperatorModel.Eigen H E ψ ∧ (∀ e ∈ OperatorModel.spectrum H, E ≤ e) ∧
    OperatorModel.multiplicity H E = 1

theorem time_reversal (forms : StandardClosedFormLibrary) (spectral : StandardAntiunitaryLibrary)
    (N : ℕ) (H : System N) (A : Point → Point) (V : Configuration N → ℝ) (b E : ℝ)
    (hH : Facts N H A V b) (ψ : State N) (hψ : GroundState N H E ψ) :
    Facts N (reverseOperator N H) (-A) V b ∧
    GroundState N (reverseOperator N H) E (conjugation N ψ) ∧
    ‖conjugation N ψ‖ = ‖ψ‖ := by
  have hs := spectral N H hH.1
  refine ⟨forms N H A V b hH (core_conjugate N) (form_conjugate N A _),
    ⟨reverse_eigen N H E ψ hψ.1, ?_, ?_⟩, (conjugation N).norm_map ψ⟩
  · simpa only [hs.1] using hψ.2.1
  · simpa only [hs.2] using hψ.2.2

theorem hamiltonian_time_reversal
    (forms : StandardClosedFormLibrary) (spectral : StandardAntiunitaryLibrary)
    (N : ℕ) (H : System N) (A : Point → Point) (v : Point → ℝ) (κ b E : ℝ)
    (hH : Facts N H A (hamiltonianPotential N v κ) b)
    (ψ : State N) (hψ : GroundState N H E ψ) :
    Facts N (reverseOperator N H) (-A) (hamiltonianPotential N v κ) b ∧
    GroundState N (reverseOperator N H) E (conjugation N ψ) ∧
    ‖conjugation N ψ‖ = ‖ψ‖ :=
  time_reversal forms spectral N H A _ b E hH ψ hψ

def density (N : ℕ) (f : Configuration (N + 1) → ℂ) (x : Point) : ℝ :=
  (N + 1 : ℝ) * ∫ y : Configuration N, Complex.normSq (f (Fin.cons x y))

def current (N : ℕ) (A : Point → Point) (f : Configuration (N + 1) → ℂ)
    (x : Point) (k : Fin 3) : ℝ :=
  (N + 1 : ℝ) * ∫ y : Configuration N,
    (conj (f (Fin.cons x y)) * momentum (N + 1) A f 0 k (Fin.cons x y)).re

theorem density_conjugate (N : ℕ) (f : Configuration (N + 1) → ℂ) :
    density N (fun x => conj (f x)) = density N f := by
  funext x
  simp [density]

theorem current_conjugate (N : ℕ) (A : Point → Point) (f : Configuration (N + 1) → ℂ) :
    current N (-A) (fun x => conj (f x)) = -current N A f := by
  funext x k
  simp only [current, momentum_conjugate, Pi.neg_apply, Complex.conj_conj]
  have he (y : Configuration N) :
      (f (Fin.cons x y) * -conj (momentum (N + 1) A f 0 k (Fin.cons x y))).re =
      -(conj (f (Fin.cons x y)) * momentum (N + 1) A f 0 k (Fin.cons x y)).re := by
    simp [Complex.mul_re]
  simp_rw [he]
  rw [integral_neg]
  ring

/-- Literal weak covariant derivative. The testing identity uses real smooth
compactly supported tests and includes integrability of both tested terms,
so it does not exploit the totalized value of a nonintegrable integral. -/
def WeakMomentum (N : ℕ) (A : Point → Point) (f : Configuration N → ℂ)
    (p : Fin N → Fin 3 → Configuration N → ℂ) : Prop :=
  ∀ i k (η : Configuration N → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
    Integrable (fun x => p i k x * (η x : ℂ)) ∧
    Integrable (fun x => Complex.I * f x * (fderiv ℝ η x (direction N i k) : ℂ) +
      (A (x i) k : ℂ) * f x * (η x : ℂ)) ∧
    (∫ x, p i k x * (η x : ℂ)) =
      ∫ x, Complex.I * f x * (fderiv ℝ η x (direction N i k) : ℂ) +
        (A (x i) k : ℂ) * f x * (η x : ℂ)

theorem weakMomentum_conjugate (N : ℕ) (A : Point → Point)
    (f : Configuration N → ℂ) (p : Fin N → Fin 3 → Configuration N → ℂ)
    (hp : WeakMomentum N A f p) :
    WeakMomentum N (-A) (fun x => conj (f x)) (fun i k x => -conj (p i k x)) := by
  intro i k η hη hc
  obtain ⟨h₁, h₂, he⟩ := hp i k η hη hc
  have hl : (fun x => -conj (p i k x) * (η x : ℂ)) =
      fun x => -conj (p i k x * (η x : ℂ)) := by
    funext x
    simp
  have hr : (fun x => Complex.I * conj (f x) * (fderiv ℝ η x (direction N i k) : ℂ) +
      ((-A) (x i) k : ℂ) * conj (f x) * (η x : ℂ)) =
      fun x => -conj (Complex.I * f x * (fderiv ℝ η x (direction N i k) : ℂ) +
        (A (x i) k : ℂ) * f x * (η x : ℂ)) := by
    funext x
    simp only [Pi.neg_apply, Complex.ofReal_neg, map_add, map_mul,
      Complex.conj_I, Complex.conj_ofReal]
    ring
  change Integrable _ (volume : Measure (Configuration N)) ∧
    Integrable _ (volume : Measure (Configuration N)) ∧ _
  rw [hl, hr]
  refine ⟨((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h₁).neg,
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h₂).neg, ?_⟩
  rw [integral_neg, integral_neg, integral_conj, integral_conj, he]

def weakCurrent (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) (x : Point) (k : Fin 3) : ℝ :=
  (N + 1 : ℝ) * ∫ y : Configuration N,
    (conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)).re

theorem weakCurrent_conjugate (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) :
    weakCurrent N (fun x => conj (f x)) (fun i k x => -conj (p i k x)) =
      -weakCurrent N f p := by
  funext x k
  simp only [weakCurrent, Complex.conj_conj, Pi.neg_apply]
  have he (y : Configuration N) :
      (f (Fin.cons x y) * -conj (p 0 k (Fin.cons x y))).re =
      -(conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)).re := by simp [Complex.mul_re]
  simp_rw [he]
  rw [integral_neg]
  ring

/-- General-N ground-state transport with the actual weak-momentum current.
The conjugated function is a representative of the transported L² state.
No pointwise differentiability of the ground-state representative is needed. -/
theorem time_reversal_with_current
    (forms : StandardClosedFormLibrary) (spectral : StandardAntiunitaryLibrary)
    (N : ℕ)
    (H : System (N + 1)) (A : Point → Point) (V : Configuration (N + 1) → ℝ) (b E : ℝ)
    (hH : Facts (N + 1) H A V b) (ψ : State (N + 1)) (hψ : GroundState (N + 1) H E ψ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ)
    (hp : ∀ i k, MemLp (p i k) 2 volume)
    (hw : WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p) :
    Facts (N + 1) (reverseOperator (N + 1) H) (-A) V b ∧
    GroundState (N + 1) (reverseOperator (N + 1) H) E (conjugation (N + 1) ψ) ∧
    ∃ p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ,
      (∀ i k, MemLp (p i k) 2 volume) ∧
      WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p ∧
      WeakMomentum (N + 1) (-A) (fun x => conj ((ψ : FullState (N + 1)) x))
        (fun i k x => -conj (p i k x)) ∧
      density N (fun x => conj ((ψ : FullState (N + 1)) x)) = density N (ψ : FullState (N + 1)) ∧
      weakCurrent N (fun x => conj ((ψ : FullState (N + 1)) x)) (fun i k x => -conj (p i k x)) =
        -weakCurrent N (ψ : FullState (N + 1)) p := by
  obtain ⟨hF, hground, _⟩ := time_reversal forms spectral (N + 1) H A V b E hH ψ hψ
  exact ⟨hF, hground, p, hp, hw, weakMomentum_conjugate _ _ _ _ hw,
    density_conjugate _ _, weakCurrent_conjugate _ _ _⟩

end MagHK.ManyBodyTimeReversal
