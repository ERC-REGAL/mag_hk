import MagHK.MonopoleRealization
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The north/south phase intertwines the literal covariant derivatives.
Density and the local current kernels consequently glue across the overlap. -/
noncomputable section
namespace MagHK.MonopoleTransition
open MagHK.MonopoleRealization MagHK.MonopoleAngular
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

theorem transition_derivative (q : ℤ) (φ : ℝ) :
    HasDerivAt (transition q) (Complex.I * (q : ℂ) * transition q φ) φ := by
  have h := (((hasDerivAt_id φ).ofReal_comp).const_mul (Complex.I * (q : ℂ))).cexp
  convert h using 1
  · ext t
    simp [transition]
  · simp only [transition, id_eq, Complex.ofReal_one, mul_one]
    push_cast
    ring

theorem south_Dr (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f) (x : Chart) :
    Dr (southRepresentative q f) x = transition q x.2.2 * Dr f x := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => f (r, x.2)) x.1 :=
    (hf.comp (differentiable_id.prodMk (differentiable_const x.2))) x.1
  simpa only [Dr, southRepresentative] using
    (hd.hasDerivAt.const_mul (transition q x.2.2)).deriv

theorem south_Dmu (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f) (x : Chart) :
    Dmu (southRepresentative q f) x = transition q x.2.2 * Dmu f x := by
  have hd : DifferentiableAt ℝ (fun μ : ℝ => f (x.1, μ, x.2.2)) x.2.1 :=
    (hf.comp ((differentiable_const x.1).prodMk
      (differentiable_id.prodMk (differentiable_const x.2.2)))) x.2.1
  simpa only [Dmu, Dμ, southRepresentative] using
    (hd.hasDerivAt.const_mul (transition q x.2.2)).deriv

theorem south_Dphi (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f) (x : Chart) :
    Dphi (southRepresentative q f) x =
      Complex.I * (q : ℂ) * transition q x.2.2 * f x + transition q x.2.2 * Dphi f x := by
  have h := (transition_derivative q x.2.2).mul
    ((hf.comp ((differentiable_const x.1).prodMk
      ((differentiable_const x.2.1).prodMk differentiable_id))) x.2.2).hasDerivAt
  exact h.deriv

def southMagneticPhi (q : ℤ) (f : Chart → ℂ) (x : Chart) : ℂ :=
  -Complex.I * Dphi f x + (southCoefficient q x.2.1 : ℂ) * f x

theorem south_magneticPhi (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f) (x : Chart) :
    southMagneticPhi q (southRepresentative q f) x = transition q x.2.2 * magneticPhi q f x := by
  rw [southMagneticPhi, south_Dphi q f hf]
  simp only [southRepresentative, magneticPhi, northCoefficient, southCoefficient]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

def southFrameDerivative (q : ℤ) (k : Fin 3) (f : Chart → ℂ) (x : Chart) : ℂ :=
  if k = 0 then -Complex.I * Dr f x
  else if k = 1 then Complex.I * (Real.sqrt (1 - x.2.1 ^ 2) / x.1 : ℝ) * Dmu f x
  else southMagneticPhi q f x / (x.1 * Real.sqrt (1 - x.2.1 ^ 2) : ℝ)

theorem south_frame (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f) (k : Fin 3) (x : Chart) :
    southFrameDerivative q k (southRepresentative q f) x =
      transition q x.2.2 * frameDerivative q k f x := by
  unfold southFrameDerivative frameDerivative
  split_ifs
  · rw [south_Dr q f hf]
    ring
  · rw [south_Dmu q f hf]
    ring
  · rw [south_magneticPhi q f hf]
    ring

theorem transition_conj_mul (q : ℤ) (φ : ℝ) : conj (transition q φ) * transition q φ = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, transition_norm]
  norm_num

theorem density_glues (q : ℤ) (f : Chart → ℂ) (x : Chart) :
    Complex.normSq (southRepresentative q f x) = Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq, southRepresentative_norm, Complex.normSq_eq_norm_sq]

theorem current_kernel_glues (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f)
    (k : Fin 3) (x : Chart) :
    conj (southRepresentative q f x) * southFrameDerivative q k (southRepresentative q f) x =
      conj (f x) * frameDerivative q k f x := by
  rw [south_frame q f hf]
  simp only [southRepresentative, map_mul]
  calc
    _ = (conj (transition q x.2.2) * transition q x.2.2) *
      (conj (f x) * frameDerivative q k f x) := by ring
    _ = _ := by rw [transition_conj_mul, one_mul]

theorem current_glues (q : ℤ) (f : Chart → ℂ) (hf : Differentiable ℝ f)
    (k : Fin 3) (x : Chart) :
    (conj (southRepresentative q f x) *
      southFrameDerivative q k (southRepresentative q f) x).re =
    (conj (f x) * frameDerivative q k f x).re := by rw [current_kernel_glues q f hf]

end MagHK.MonopoleTransition
