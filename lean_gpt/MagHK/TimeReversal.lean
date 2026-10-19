import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Time reversal, manuscript Lemma `lem:time-reversal`.

The density and current identities below use actual complex functions and
Bochner integrals. The spectral transport theorem is stated for normalized
states with an energy functional. Its energy-intertwining premise is the
standard antiunitary equivalence fact, not an assumption of ground-state
uniqueness on the reversed system.
-/

namespace MagHK.TimeReversal

open MeasureTheory

variable {X Y S T : Type*} [MeasurableSpace Y]

noncomputable def density (μ : Measure Y) (ψ : X → Y → ℂ) (x : X) : ℝ :=
  2 * ∫ y, Complex.normSq (ψ x y) ∂μ

noncomputable def paramagnetic (μ : Measure Y) (ψ dψ : X → Y → ℂ) (x : X) : ℝ :=
  2 * ∫ y, (star (ψ x y) * dψ x y).im ∂μ

noncomputable def current (μ : Measure Y) (ψ dψ : X → Y → ℂ)
    (A : X → ℝ) (x : X) : ℝ :=
  paramagnetic μ ψ dψ x + density μ ψ x * A x

theorem conjugate_density (μ : Measure Y) (ψ : X → Y → ℂ) :
    density μ (fun x y => star (ψ x y)) = density μ ψ := by
  funext x
  simp [density]

theorem conjugate_paramagnetic (μ : Measure Y) (ψ dψ : X → Y → ℂ) :
    paramagnetic μ (fun x y => star (ψ x y)) (fun x y => star (dψ x y)) =
      -paramagnetic μ ψ dψ := by
  funext x
  simp only [paramagnetic, Pi.neg_apply]
  have h (y : Y) : (star (star (ψ x y)) * star (dψ x y)).im =
      -(star (ψ x y) * dψ x y).im := by
    simp [Complex.mul_im]
    ring
  simp_rw [h]
  rw [integral_neg]
  ring

theorem conjugate_current (μ : Measure Y) (ψ dψ : X → Y → ℂ) (A : X → ℝ) :
    current μ (fun x y => star (ψ x y)) (fun x y => star (dψ x y)) (-A) =
      -current μ ψ dψ A := by
  funext x
  simp only [current, congrFun (conjugate_density μ ψ) x,
    congrFun (conjugate_paramagnetic μ ψ dψ) x, Pi.neg_apply]
  ring

theorem conjugate_zero_current (μ : Measure Y) (ψ dψ : X → Y → ℂ) (A : X → ℝ)
    (h : current μ ψ dψ A = 0) :
    current μ (fun x y => star (ψ x y)) (fun x y => star (dψ x y)) (-A) = 0 := by
  rw [conjugate_current, h, neg_zero]

theorem conjugate_antisymmetric (ψ : X → X → ℂ)
    (h : ∀ x y, ψ x y = -ψ y x) :
    ∀ x y, star (ψ x y) = -star (ψ y x) := by
  intro x y
  rw [h x y, star_neg]

def IsGround (energy : S → ℝ) (s : S) : Prop := ∀ t, energy s ≤ energy t

def IsNondegenerateGround (energy : S → ℝ) (sameRay : S → S → Prop) (s : S) : Prop :=
  IsGround energy s ∧ ∀ t, IsGround energy t → sameRay t s

theorem transport_ground (K : S ≃ T) (E : S → ℝ) (E' : T → ℝ)
    (hE : ∀ s, E' (K s) = E s) (s : S) (hs : IsGround E s) :
    IsGround E' (K s) := by
  intro t
  obtain ⟨u, rfl⟩ := K.surjective t
  simpa only [hE] using hs u

theorem transport_nondegenerate (K : S ≃ T) (E : S → ℝ) (E' : T → ℝ)
    (R : S → S → Prop) (R' : T → T → Prop)
    (hE : ∀ s, E' (K s) = E s) (hR : ∀ s t, R s t → R' (K s) (K t))
    (s : S) (hs : IsNondegenerateGround E R s) :
    IsNondegenerateGround E' R' (K s) := by
  refine ⟨transport_ground K E E' hE s hs.1, ?_⟩
  intro t ht
  obtain ⟨u, rfl⟩ := K.surjective t
  apply hR u s
  apply hs.2 u
  intro v
  have h := ht (K v)
  simpa only [hE] using h

/-- A gauge-invariant nonzero real magnetic component distinguishes opposite fields. -/
theorem opposite_fields_inequivalent (A : S) (reverse : S → S)
    (B : S → X → ℝ) (Gauge : S → S → Prop)
    (gauge_preserves : ∀ a b, Gauge a b → B a = B b)
    (reverses : B (reverse A) = -B A) (nonzero : B A ≠ 0) :
    ¬Gauge A (reverse A) := by
  intro hg
  have h := gauge_preserves A (reverse A) hg
  rw [reverses] at h
  apply nonzero
  funext x
  have hx := congrFun h x
  simp only [Pi.neg_apply] at hx
  simp only [Pi.zero_apply]
  linarith

end MagHK.TimeReversal
