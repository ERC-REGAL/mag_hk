import MagHK.TimeReversal
import Mathlib.Algebra.BigOperators.Field

/-!
Time reversal for actual magnetic quadratic-form integrands and normalized
function states. Domain preservation and conjugation of weak derivatives
are explicit analytic inputs. Energy preservation is proved, not assumed.
The correspondence between form minimizers and operator ground states is
one of the standard operator-theory facts permitted by the user.
-/

namespace MagHK.MagneticForms

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def conjugate (ψ : X → ℂ) : X → ℂ := fun x => star (ψ x)

noncomputable def kineticDensity (ψ : X → ℂ) (dψ : Fin n → X → ℂ)
    (A : Fin n → X → ℝ) (x : X) : ℝ :=
  ∑ i, Complex.normSq (-Complex.I * dψ i x + (A i x : ℂ) * ψ x)

noncomputable def formEnergy (μ : Measure X) (ψ : X → ℂ)
    (dψ : Fin n → X → ℂ) (A : Fin n → X → ℝ) (V : X → ℝ) : ℝ :=
  ∫ x, kineticDensity ψ dψ A x + V x * Complex.normSq (ψ x) ∂μ

noncomputable def mass (μ : Measure X) (ψ : X → ℂ) : ℝ :=
  ∫ x, Complex.normSq (ψ x) ∂μ

theorem conjugate_involutive : Function.Involutive (@conjugate X) := by
  intro ψ
  funext x
  simp [conjugate]

theorem magnetic_momentum_conjugate (ψ dψ : ℂ) (a : ℝ) :
    -Complex.I * star dψ + ((-a : ℝ) : ℂ) * star ψ =
      -star (-Complex.I * dψ + (a : ℂ) * ψ) := by
  simp only [star_add, star_mul, star_neg, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem conjugate_kineticDensity (ψ : X → ℂ) (dψ : Fin n → X → ℂ)
    (A : Fin n → X → ℝ) :
    kineticDensity (conjugate ψ) (fun i => conjugate (dψ i)) (-A) =
      kineticDensity ψ dψ A := by
  funext x
  apply Finset.sum_congr rfl
  intro i hi
  change Complex.normSq (-Complex.I * star (dψ i x) +
    ((-A i x : ℝ) : ℂ) * star (ψ x)) = _
  rw [magnetic_momentum_conjugate]
  exact (Complex.normSq_neg _).trans (Complex.normSq_conj _)

theorem conjugate_formEnergy (μ : Measure X) (ψ : X → ℂ)
    (dψ : Fin n → X → ℂ) (A : Fin n → X → ℝ) (V : X → ℝ) :
    formEnergy μ (conjugate ψ) (fun i => conjugate (dψ i)) (-A) V =
      formEnergy μ ψ dψ A V := by
  unfold formEnergy
  rw [conjugate_kineticDensity]
  simp [conjugate]

theorem conjugate_mass (μ : Measure X) (ψ : X → ℂ) :
    mass μ (conjugate ψ) = mass μ ψ := by
  simp [mass, conjugate]

def NormalizedState (μ : Measure X) (domain : (X → ℂ) → Prop) :=
  {ψ : X → ℂ // domain ψ ∧ mass μ ψ = 1}

def SameRay (ψ φ : X → ℂ) : Prop :=
  ∃ c : ℂ, Complex.normSq c = 1 ∧ ∀ x, ψ x = c * φ x

theorem conjugate_sameRay {ψ φ : X → ℂ} (h : SameRay ψ φ) :
    SameRay (conjugate ψ) (conjugate φ) := by
  obtain ⟨c, hc, heq⟩ := h
  refine ⟨star c, by simpa using hc, ?_⟩
  intro x
  simp only [conjugate, heq x, star_mul]
  exact mul_comm _ _

noncomputable def normalizedConjugation (μ : Measure X)
    (domain : (X → ℂ) → Prop)
    (hdom : ∀ ψ, domain ψ → domain (conjugate ψ)) :
    NormalizedState μ domain ≃ NormalizedState μ domain where
  toFun ψ := ⟨conjugate ψ.1, hdom ψ.1 ψ.2.1,
    (conjugate_mass μ ψ.1).trans ψ.2.2⟩
  invFun ψ := ⟨conjugate ψ.1, hdom ψ.1 ψ.2.1,
    (conjugate_mass μ ψ.1).trans ψ.2.2⟩
  left_inv ψ := Subtype.ext (conjugate_involutive ψ.1)
  right_inv ψ := Subtype.ext (conjugate_involutive ψ.1)

/-- Nondegenerate form ground states are transported by conjugation for
the literal magnetic energy functional. The two analytic premises apply
to every state in the chosen form domain, independently of ground states. -/
theorem conjugate_nondegenerate_form_ground (μ : Measure X)
    (domain : (X → ℂ) → Prop)
    (D : (X → ℂ) → Fin n → X → ℂ)
    (A : Fin n → X → ℝ) (V : X → ℝ)
    (hdom : ∀ ψ, domain ψ → domain (conjugate ψ))
    (hD : ∀ ψ, domain ψ → D (conjugate ψ) = fun i => conjugate (D ψ i))
    (ψ : NormalizedState μ domain)
    (hψ : MagHK.TimeReversal.IsNondegenerateGround
      (fun φ : NormalizedState μ domain => formEnergy μ φ.1 (D φ.1) A V)
      (fun φ χ => SameRay φ.1 χ.1) ψ) :
    MagHK.TimeReversal.IsNondegenerateGround
      (fun φ : NormalizedState μ domain => formEnergy μ φ.1 (D φ.1) (-A) V)
      (fun φ χ => SameRay φ.1 χ.1)
      (normalizedConjugation μ domain hdom ψ) := by
  apply MagHK.TimeReversal.transport_nondegenerate
    (normalizedConjugation μ domain hdom)
    (fun φ : NormalizedState μ domain => formEnergy μ φ.1 (D φ.1) A V)
    (fun φ : NormalizedState μ domain => formEnergy μ φ.1 (D φ.1) (-A) V)
    (fun φ χ => SameRay φ.1 χ.1)
    (fun φ χ => SameRay φ.1 χ.1)
  · intro φ
    change formEnergy μ (conjugate φ.1) (D (conjugate φ.1)) (-A) V = _
    rw [hD φ.1 φ.2.1, conjugate_formEnergy]
  · intro φ χ h
    exact conjugate_sameRay h
  · exact hψ

end MagHK.MagneticForms
