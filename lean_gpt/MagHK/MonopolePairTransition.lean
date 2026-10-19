import MagHK.MonopoleTransition

/-! North/south transition for the actual two-particle covariant derivatives
and local density and current kernels. -/
noncomputable section
namespace MagHK.MonopoleTransition
open MagHK.MonopoleRealization MagHK.MonopoleAngular
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

def pairTransition (q : ℤ) (p : Chart × Chart) : ℂ :=
  transition q p.1.2.2 * transition q p.2.2.2

def southPairRepresentative (q : ℤ) (f : Chart × Chart → ℂ) (p : Chart × Chart) : ℂ :=
  pairTransition q p * f p

def southPairFrameDerivative (q : ℤ) (i : Fin 2) (k : Fin 3)
    (f : Chart × Chart → ℂ) (p : Chart × Chart) : ℂ :=
  if i = 0 then southFrameDerivative q k (fun x => f (x, p.2)) p.1
  else southFrameDerivative q k (fun y => f (p.1, y)) p.2

theorem frame_const_mul (q : ℤ) (k : Fin 3) (f : Chart → ℂ) (c : ℂ) (x : Chart) :
    frameDerivative q k (fun y => c * f y) x = c * frameDerivative q k f x := by
  unfold frameDerivative
  split_ifs
  · simp only [Dr, deriv_const_mul_field (𝕜 := ℝ)]
    ring
  · simp only [Dmu, Dμ, deriv_const_mul_field (𝕜 := ℝ)]
    ring
  · simp only [magneticPhi, Dphi, Dφ, deriv_const_mul_field (𝕜 := ℝ)]
    ring

theorem south_pair_frame (q : ℤ) (f : Chart × Chart → ℂ) (hf : Differentiable ℝ f)
    (i : Fin 2) (k : Fin 3) (p : Chart × Chart) :
    southPairFrameDerivative q i k (southPairRepresentative q f) p =
      pairTransition q p * pairFrameDerivative q i k f p := by
  unfold southPairFrameDerivative pairFrameDerivative
  split_ifs
  · have he : (fun x => southPairRepresentative q f (x, p.2)) =
        southRepresentative q (fun x => transition q p.2.2.2 * f (x, p.2)) := by
      funext x
      dsimp only [southPairRepresentative, pairTransition, southRepresentative]
      ring
    have hs : Differentiable ℝ (fun x : Chart => transition q p.2.2.2 * f (x, p.2)) :=
      (hf.comp (differentiable_id.prodMk (differentiable_const p.2))).const_mul _
    rw [he, south_frame q (fun x => transition q p.2.2.2 * f (x, p.2)) hs k p.1,
      frame_const_mul]
    dsimp only [pairTransition]
    ring
  · have he : (fun y => southPairRepresentative q f (p.1, y)) =
        southRepresentative q (fun y => transition q p.1.2.2 * f (p.1, y)) := by
      funext y
      dsimp only [southPairRepresentative, pairTransition, southRepresentative]
      ring
    have hs : Differentiable ℝ (fun y : Chart => transition q p.1.2.2 * f (p.1, y)) :=
      (hf.comp ((differentiable_const p.1).prodMk differentiable_id)).const_mul _
    rw [he, south_frame q (fun y => transition q p.1.2.2 * f (p.1, y)) hs k p.2,
      frame_const_mul]
    dsimp only [pairTransition]
    ring

theorem pairTransition_conj_mul (q : ℤ) (p : Chart × Chart) :
    conj (pairTransition q p) * pairTransition q p = 1 := by
  simp only [pairTransition, map_mul]
  calc
    _ = (conj (transition q p.1.2.2) * transition q p.1.2.2) *
      (conj (transition q p.2.2.2) * transition q p.2.2.2) := by ring
    _ = _ := by rw [transition_conj_mul, transition_conj_mul, one_mul]

theorem pairTransition_normSq (q : ℤ) (p : Chart × Chart) :
    Complex.normSq (pairTransition q p) = 1 := by
  have h := pairTransition_conj_mul q p
  rw [← Complex.normSq_eq_conj_mul_self] at h
  exact_mod_cast h

theorem pair_density_glues (q : ℤ) (f : Chart × Chart → ℂ) (p : Chart × Chart) :
    Complex.normSq (southPairRepresentative q f p) = Complex.normSq (f p) := by
  rw [southPairRepresentative, Complex.normSq_mul, pairTransition_normSq, one_mul]

theorem pair_current_kernel_glues (q : ℤ) (f : Chart × Chart → ℂ)
    (hf : Differentiable ℝ f) (i : Fin 2) (k : Fin 3) (p : Chart × Chart) :
    conj (southPairRepresentative q f p) *
      southPairFrameDerivative q i k (southPairRepresentative q f) p =
      conj (f p) * pairFrameDerivative q i k f p := by
  rw [south_pair_frame q f hf]
  simp only [southPairRepresentative, map_mul]
  calc
    _ = (conj (pairTransition q p) * pairTransition q p) *
      (conj (f p) * pairFrameDerivative q i k f p) := by ring
    _ = _ := by rw [pairTransition_conj_mul, one_mul]

theorem pair_current_glues (q : ℤ) (f : Chart × Chart → ℂ)
    (hf : Differentiable ℝ f) (i : Fin 2) (k : Fin 3) (p : Chart × Chart) :
    (conj (southPairRepresentative q f p) *
      southPairFrameDerivative q i k (southPairRepresentative q f) p).re =
      (conj (f p) * pairFrameDerivative q i k f p).re := by
  rw [pair_current_kernel_glues q f hf]

end MagHK.MonopoleTransition
