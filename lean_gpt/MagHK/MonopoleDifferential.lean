import MagHK.MonopoleRealization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Actual angular differential operators and their Casimir. -/
noncomputable section
namespace MagHK.MonopoleDifferential
open MagHK.MonopoleRealization MagHK.MonopoleAngular MagHK.MonopoleTrial Set Filter
open scoped ContDiff Topology
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

def sine (μ : ℝ) : ℝ := Real.sqrt (1 - μ ^ 2)
private theorem sine_pos (μ : ℝ) (hμ : μ ∈ Ioo (-1 : ℝ) 1) : 0 < sine μ :=
  Real.sqrt_pos.mpr (by nlinarith [hμ.1, hμ.2])
private theorem sine_sq (μ : ℝ) (hμ : μ ∈ Ioo (-1 : ℝ) 1) : sine μ ^ 2 = 1 - μ ^ 2 :=
  Real.sq_sqrt (by nlinarith [hμ.1, hμ.2])
private theorem sine_derivative (μ : ℝ) (hμ : μ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt sine (-μ / sine μ) μ := by
  apply ((((hasDerivAt_id μ).pow 2).const_sub 1).sqrt
    (by nlinarith [hμ.1, hμ.2] : 1 - μ ^ 2 ≠ 0)).congr_deriv
  dsimp [sine]
  ring

def firstOrder (a b c : Angle → ℂ) (Y : Angle → ℂ) (p : Angle) : ℂ :=
  a p * Dμ Y p + b p * Dφ Y p + c p * Y p

/-- Ordinary local differentiability assumptions for composing first-order
operators. No spectral or geometric conclusion is an input. -/
structure TwiceDifferentiable (Y : Angle → ℂ) (p : Angle) : Prop where
  value : DifferentiableAt ℝ Y p
  mu : DifferentiableAt ℝ (Dμ Y) p
  phi : DifferentiableAt ℝ (Dφ Y) p

private theorem slice_mu {Y : Angle → ℂ} {p : Angle} (hY : DifferentiableAt ℝ Y p) :
    HasDerivAt (fun μ => Y (μ, p.2)) (Dμ Y p) p.1 := by
  exact (hY.comp p.1 ((differentiableAt_id).prodMk (differentiableAt_const p.2))).hasDerivAt
private theorem slice_phi {Y : Angle → ℂ} {p : Angle} (hY : DifferentiableAt ℝ Y p) :
    HasDerivAt (fun φ => Y (p.1, φ)) (Dφ Y p) p.2 := by
  exact (hY.comp p.2 ((differentiableAt_const p.1).prodMk differentiableAt_id)).hasDerivAt

private theorem firstOrder_mu (a b c Y : Angle → ℂ) (p : Angle)
    (ha : HasDerivAt (fun μ => a (μ, p.2)) (Dμ a p) p.1)
    (hb : HasDerivAt (fun μ => b (μ, p.2)) (Dμ b p) p.1)
    (hc : HasDerivAt (fun μ => c (μ, p.2)) (Dμ c p) p.1)
    (hY : TwiceDifferentiable Y p) :
    Dμ (firstOrder a b c Y) p =
      Dμ a p * Dμ Y p + a p * Dμ (Dμ Y) p +
      (Dμ b p * Dφ Y p + b p * Dμ (Dφ Y) p) +
      (Dμ c p * Y p + c p * Dμ Y p) := by
  exact (((ha.mul (slice_mu hY.mu)).add (hb.mul (slice_mu hY.phi))).add
    (hc.mul (slice_mu hY.value))).deriv
private theorem firstOrder_phi (a b c Y : Angle → ℂ) (p : Angle)
    (ha : HasDerivAt (fun φ => a (p.1, φ)) (Dφ a p) p.2)
    (hb : HasDerivAt (fun φ => b (p.1, φ)) (Dφ b p) p.2)
    (hc : HasDerivAt (fun φ => c (p.1, φ)) (Dφ c p) p.2)
    (hY : TwiceDifferentiable Y p) :
    Dφ (firstOrder a b c Y) p =
      Dφ a p * Dμ Y p + a p * Dφ (Dμ Y) p +
      (Dφ b p * Dφ Y p + b p * Dφ (Dφ Y) p) +
      (Dφ c p * Y p + c p * Dφ Y p) := by
  exact (((ha.mul (slice_phi hY.mu)).add (hb.mul (slice_phi hY.phi))).add
    (hc.mul (slice_phi hY.value))).deriv

/-- Components are ordered as z, x, y. -/
def angularMu (k : Fin 3) (p : Angle) : ℂ :=
  if k = 0 then 0 else if k = 1 then -Complex.I * sine p.1 * Real.sin p.2
  else Complex.I * sine p.1 * Real.cos p.2

def angularPhi (k : Fin 3) (p : Angle) : ℂ :=
  if k = 0 then -Complex.I else if k = 1 then Complex.I * (p.1 * Real.cos p.2 / sine p.1 : ℝ)
  else Complex.I * (p.1 * Real.sin p.2 / sine p.1 : ℝ)

def angularValue (g : ℝ) (k : Fin 3) (p : Angle) : ℂ :=
  if k = 0 then g else if k = 1 then g * ((1 - p.1) * Real.cos p.2 / sine p.1 : ℝ)
  else g * ((1 - p.1) * Real.sin p.2 / sine p.1 : ℝ)

def angularMomentum (g : ℝ) (k : Fin 3) : (Angle → ℂ) → Angle → ℂ :=
  firstOrder (angularMu k) (angularPhi k) (angularValue g k)

def angularSquare (g : ℝ) (Y : Angle → ℂ) (p : Angle) : ℂ :=
  ∑ k : Fin 3, angularMomentum g k (angularMomentum g k Y) p

private theorem mu_over_sine (μ : ℝ) (hμ : μ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => t / sine t) (1 / sine μ ^ 3) μ := by
  apply ((hasDerivAt_id μ).div (sine_derivative μ hμ) (sine_pos μ hμ).ne').congr_deriv
  dsimp
  field_simp [(sine_pos μ hμ).ne']
  nlinarith [sine_sq μ hμ]

private theorem one_sub_over_sine (μ : ℝ) (hμ : μ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => (1 - t) / sine t) (-(1 - μ) / sine μ ^ 3) μ := by
  apply (((hasDerivAt_id μ).const_sub 1).div (sine_derivative μ hμ)
    (sine_pos μ hμ).ne').congr_deriv
  dsimp
  field_simp [(sine_pos μ hμ).ne']
  nlinarith [sine_sq μ hμ]

private theorem angularMu_mu (k : Fin 3) (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun μ => angularMu k (μ, p.2))
      (if k = 0 then 0 else if k = 1 then Complex.I * (p.1 / sine p.1 : ℝ) * Real.sin p.2
       else -Complex.I * (p.1 / sine p.1 : ℝ) * Real.cos p.2) p.1 := by
  fin_cases k <;> norm_num only [angularMu, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · convert! (((sine_derivative p.1 hp).ofReal_comp.const_mul (-Complex.I)).mul_const
      (Real.sin p.2 : ℂ)) using 1
    simp only [Complex.ofReal_div, Complex.ofReal_neg]
    ring
  · convert! (((sine_derivative p.1 hp).ofReal_comp.const_mul Complex.I).mul_const
      (Real.cos p.2 : ℂ)) using 1
    simp only [Complex.ofReal_div, Complex.ofReal_neg]
    ring

private theorem angularPhi_mu (k : Fin 3) (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun μ => angularPhi k (μ, p.2))
      (if k = 0 then 0 else if k = 1 then Complex.I * (Real.cos p.2 / sine p.1 ^ 3 : ℝ)
       else Complex.I * (Real.sin p.2 / sine p.1 ^ 3 : ℝ)) p.1 := by
  fin_cases k <;> norm_num only [angularPhi, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · convert! ((mu_over_sine p.1 hp).mul_const (Real.cos p.2)).ofReal_comp.const_mul Complex.I using 1
    · ext t; congr 2; ring
    · congr 1; push_cast; ring
  · convert! ((mu_over_sine p.1 hp).mul_const (Real.sin p.2)).ofReal_comp.const_mul Complex.I using 1
    · ext t; congr 2; ring
    · congr 1; push_cast; ring

private theorem angularValue_mu (g : ℝ) (k : Fin 3) (p : Angle)
    (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun μ => angularValue g k (μ, p.2))
      (if k = 0 then 0 else if k = 1 then (-g * (1 - p.1) * Real.cos p.2 / sine p.1 ^ 3 : ℝ)
       else (-g * (1 - p.1) * Real.sin p.2 / sine p.1 ^ 3 : ℝ)) p.1 := by
  fin_cases k <;> norm_num only [angularValue, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · convert! ((one_sub_over_sine p.1 hp).mul_const (Real.cos p.2)).ofReal_comp.const_mul (g : ℂ) using 1
    · ext t; congr 2; ring
    · push_cast; ring
  · convert! ((one_sub_over_sine p.1 hp).mul_const (Real.sin p.2)).ofReal_comp.const_mul (g : ℂ) using 1
    · ext t; congr 2; ring
    · push_cast; ring

private theorem angularMu_phi (k : Fin 3) (p : Angle) :
    HasDerivAt (fun φ => angularMu k (p.1, φ))
      (if k = 0 then 0 else if k = 1 then -Complex.I * sine p.1 * Real.cos p.2
       else -Complex.I * sine p.1 * Real.sin p.2) p.2 := by
  fin_cases k <;> norm_num only [angularMu, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · exact (Real.hasDerivAt_sin p.2).ofReal_comp.const_mul (-Complex.I * sine p.1)
  · convert! (Real.hasDerivAt_cos p.2).ofReal_comp.const_mul (Complex.I * sine p.1) using 1
    simp only [Complex.ofReal_neg]; ring

private theorem angularPhi_phi (k : Fin 3) (p : Angle) :
    HasDerivAt (fun φ => angularPhi k (p.1, φ))
      (if k = 0 then 0 else if k = 1 then -Complex.I * (p.1 * Real.sin p.2 / sine p.1 : ℝ)
       else Complex.I * (p.1 * Real.cos p.2 / sine p.1 : ℝ)) p.2 := by
  fin_cases k <;> norm_num only [angularPhi, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · convert! (((Real.hasDerivAt_cos p.2).const_mul p.1).div_const (sine p.1)).ofReal_comp.const_mul
      Complex.I using 1
    push_cast; ring
  · exact (((Real.hasDerivAt_sin p.2).const_mul p.1).div_const
      (sine p.1)).ofReal_comp.const_mul Complex.I

private theorem angularValue_phi (g : ℝ) (k : Fin 3) (p : Angle) :
    HasDerivAt (fun φ => angularValue g k (p.1, φ))
      (if k = 0 then 0 else if k = 1 then (-g * (1 - p.1) * Real.sin p.2 / sine p.1 : ℝ)
       else (g * (1 - p.1) * Real.cos p.2 / sine p.1 : ℝ)) p.2 := by
  fin_cases k <;> norm_num only [angularValue, Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, ↓reduceIte]
  all_goals try simp only [ite_true, ite_false]
  · exact hasDerivAt_const _ _
  · convert! (((Real.hasDerivAt_cos p.2).const_mul (1 - p.1)).div_const
      (sine p.1)).ofReal_comp.const_mul (g : ℂ) using 1
    push_cast; ring
  · convert! (((Real.hasDerivAt_sin p.2).const_mul (1 - p.1)).div_const
      (sine p.1)).ofReal_comp.const_mul (g : ℂ) using 1
    push_cast; ring

/-- The partial derivatives agree with the ordinary Fréchet derivative. -/
theorem Dmu_eq_fderiv (Y : Angle → ℂ) (p : Angle) (hY : DifferentiableAt ℝ Y p) :
    Dμ Y p = fderiv ℝ Y p (1, 0) := by
  exact (hY.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem Dphi_eq_fderiv (Y : Angle → ℂ) (p : Angle) (hY : DifferentiableAt ℝ Y p) :
    Dφ Y p = fderiv ℝ Y p (0, 1) := by
  exact (hY.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv

theorem twiceDifferentiable_of_contDiff (Y : Angle → ℂ) (hY : ContDiff ℝ 2 Y) (p : Angle) :
    TwiceDifferentiable Y p := by
  have hd := hY.differentiable (by norm_num)
  have hm : Dμ Y = fun p => fderiv ℝ Y p (1, 0) := funext (fun p => Dmu_eq_fderiv Y p (hd p))
  have hp : Dφ Y = fun p => fderiv ℝ Y p (0, 1) := funext (fun p => Dphi_eq_fderiv Y p (hd p))
  refine ⟨hd p, ?_, ?_⟩
  · rw [hm]
    exact ((hY.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) p
  · rw [hp]
    exact ((hY.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) p

/-- Real coordinate axes are ordered as z, x, y. -/
def radialVector (p : Angle) : Fin 3 → ℂ :=
  ![p.1, (sine p.1 * Real.cos p.2 : ℝ), (sine p.1 * Real.sin p.2 : ℝ)]
def polarVector (p : Angle) : Fin 3 → ℂ :=
  ![-sine p.1, (p.1 * Real.cos p.2 : ℝ), (p.1 * Real.sin p.2 : ℝ)]
def azimuthVector (p : Angle) : Fin 3 → ℂ :=
  ![0, -Real.sin p.2, Real.cos p.2]
def cross (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- Cartesian components of the literal closed-frame expression on smooth
functions. The Cartesian chain rule identifies these with −i∇+A. -/
def momentumVector (q : ℤ) (f : Chart → ℂ) (x : Chart) (k : Fin 3) : ℂ :=
  radialVector x.2 k * frameDerivative q 0 f x +
  polarVector x.2 k * frameDerivative q 1 f x +
  azimuthVector x.2 k * frameDerivative q 2 f x

def positionVector (x : Chart) (k : Fin 3) : ℂ := (x.1 : ℂ) * radialVector x.2 k

def angularFromMomentum (q : ℤ) (f : Chart → ℂ) (x : Chart) (k : Fin 3) : ℂ :=
  cross (positionVector x) (momentumVector q f x) k +
    ((q : ℝ) / 2 : ℝ) * radialVector x.2 k * f x

/-- The explicit Cartesian cross product reproduces the angular first-order
operators, for every charge and every differentiable chart representative. -/
theorem angularFromMomentum_eq (q : ℤ) (f : Chart → ℂ) (x : Chart)
    (hr : x.1 ≠ 0) (hx : x.2.1 ∈ Ioo (-1 : ℝ) 1) (k : Fin 3) :
    angularFromMomentum q f x k = angularMomentum ((q : ℝ) / 2) k (fun p => f (x.1, p)) x.2 := by
  have hs : (sine x.2.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sine_pos x.2.1 hx).ne'
  have hrc : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hsq : (sine x.2.1 : ℂ) ^ 2 = 1 - (x.2.1 : ℂ) ^ 2 := by exact_mod_cast sine_sq x.2.1 hx
  have htrig : (Real.cos x.2.2 : ℂ) ^ 2 = 1 - (Real.sin x.2.2 : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq x.2.2] :
      Real.cos x.2.2 ^ 2 = 1 - Real.sin x.2.2 ^ 2)
  push_cast at htrig
  have hs4 : (sine x.2.1 : ℂ) ^ 4 = (1 - (x.2.1 : ℂ) ^ 2) ^ 2 := by
    rw [show (sine x.2.1 : ℂ) ^ 4 = ((sine x.2.1 : ℂ) ^ 2) ^ 2 by ring, hsq]
  have hsine : Real.sqrt (1 - x.2.1 ^ 2) = sine x.2.1 := rfl
  fin_cases k <;>
    norm_num [angularFromMomentum, cross, positionVector, momentumVector, radialVector,
      polarVector, azimuthVector, frameDerivative, angularMomentum, firstOrder,
      angularMu, angularPhi, angularValue, northCoefficient, magneticPhi,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Fin.reduceFinMk, Fin.isValue, Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      ↓reduceIte, Dmu, Dphi, hsine] <;>
    try simp only [ite_true, ite_false]
  all_goals push_cast <;> field_simp [hs, hrc] <;> ring_nf <;>
    simp only [Complex.I_sq, hs4, hsq, htrig] <;> ring

/-- The square of the actual angular momentum differential operator is the
magnetic angular Laplacian plus g². Mixed derivatives cancel directly. -/
theorem angularSquare_eq (g : ℝ) (Y : Angle → ℂ) (p : Angle)
    (hp : p.1 ∈ Ioo (-1 : ℝ) 1) (hY : TwiceDifferentiable Y p) :
    angularSquare g Y p = angularExpression g Y p + (g ^ 2 : ℝ) * Y p := by
  have hmu (k : Fin 3) := firstOrder_mu (angularMu k) (angularPhi k) (angularValue g k)
    Y p ((angularMu_mu k p hp).differentiableAt.hasDerivAt)
      ((angularPhi_mu k p hp).differentiableAt.hasDerivAt)
      ((angularValue_mu g k p hp).differentiableAt.hasDerivAt) hY
  have hphi (k : Fin 3) := firstOrder_phi (angularMu k) (angularPhi k) (angularValue g k)
    Y p ((angularMu_phi k p).differentiableAt.hasDerivAt)
      ((angularPhi_phi k p).differentiableAt.hasDerivAt)
      ((angularValue_phi g k p).differentiableAt.hasDerivAt) hY
  have hma (k : Fin 3) := (angularMu_mu k p hp).deriv
  have hmb (k : Fin 3) := (angularPhi_mu k p hp).deriv
  have hmc (k : Fin 3) := (angularValue_mu g k p hp).deriv
  have hpa (k : Fin 3) := (angularMu_phi k p).deriv
  have hpb (k : Fin 3) := (angularPhi_phi k p).deriv
  have hpc (k : Fin 3) := (angularValue_phi g k p).deriv
  change (∑ k : Fin 3, (angularMu k p * Dμ (firstOrder (angularMu k) (angularPhi k)
      (angularValue g k) Y) p + angularPhi k p * Dφ (firstOrder (angularMu k)
      (angularPhi k) (angularValue g k) Y) p + angularValue g k p *
      firstOrder (angularMu k) (angularPhi k) (angularValue g k) Y p)) = _
  simp_rw [hmu, hphi]
  change _ = angularExpression g Y p + (g ^ 2 : ℝ) * Y p
  simp only [show ∀ k, Dμ (angularMu k) p = _ from hma,
    show ∀ k, Dμ (angularPhi k) p = _ from hmb,
    show ∀ k, Dμ (angularValue g k) p = _ from hmc,
    show ∀ k, Dφ (angularMu k) p = _ from hpa,
    show ∀ k, Dφ (angularPhi k) p = _ from hpb,
    show ∀ k, Dφ (angularValue g k) p = _ from hpc]
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [Fin.sum_univ_three, firstOrder, angularMu, angularPhi, angularValue,
    h10, h20, h21, eq_self_iff_true, ite_true, ite_false]
  unfold angularExpression
  push_cast
  have hs : (sine p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sine_pos p.1 hp).ne'
  have hsq : (sine p.1 : ℂ) ^ 2 = 1 - (p.1 : ℂ) ^ 2 := by exact_mod_cast sine_sq p.1 hp
  have htrig : (Real.cos p.2 : ℂ) ^ 2 = 1 - (Real.sin p.2 : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq p.2] :
      Real.cos p.2 ^ 2 = 1 - Real.sin p.2 ^ 2)
  push_cast at htrig
  have hm : 1 - (p.1 : ℂ) ^ 2 ≠ 0 := by rw [← hsq]; exact pow_ne_zero 2 hs
  rw [← hsq]
  field_simp [hs]
  ring_nf
  have hs4 : (sine p.1 : ℂ) ^ 4 = (1 - (p.1 : ℂ) ^ 2) ^ 2 := by
    rw [show (sine p.1 : ℂ) ^ 4 = ((sine p.1 : ℂ) ^ 2) ^ 2 by ring, hsq]
  have hs6 : (sine p.1 : ℂ) ^ 6 = (1 - (p.1 : ℂ) ^ 2) ^ 3 := by
    rw [show (sine p.1 : ℂ) ^ 6 = ((sine p.1 : ℂ) ^ 2) ^ 3 by ring, hsq]
  simp only [Complex.I_sq, hs4, hs6, hsq, htrig]
  ring

theorem angularMomentum_z (g : ℝ) (Y : Angle → ℂ) (p : Angle) :
    angularMomentum g 0 Y p = -Complex.I * Dφ Y p + (g : ℂ) * Y p := by
  simp [angularMomentum, firstOrder, angularMu, angularPhi, angularValue]

theorem Yplus_projection (p : Angle) :
    angularMomentum (1 / 2) 0 Yplus p = (1 / 2 : ℂ) * Yplus p := by
  simp [angularMomentum_z]

theorem Yminus_projection (p : Angle) :
    angularMomentum (1 / 2) 0 Yminus p = (-1 / 2 : ℂ) * Yminus p := by
  rw [angularMomentum_z, Yminus_Dφ]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  <;> ring

/-- Every angular eigen-equation used by the spectral library is an
actual Casimir eigen-equation with the stated g² shift. -/
theorem angularSquare_eigenvalue (g lam : ℝ) (Y : Angle → ℂ) (p : Angle)
    (hp : p.1 ∈ Ioo (-1 : ℝ) 1) (hY : TwiceDifferentiable Y p)
    (he : angularExpression g Y p = (lam : ℂ) * Y p) :
    angularSquare g Y p = (lam + g ^ 2 : ℝ) * Y p := by
  rw [angularSquare_eq g Y p hp hY, he]
  push_cast
  ring

/-- The radial splitting with the actual Cartesian angular-momentum
square, applied to the literal spherical differential expression. -/
theorem radial_splitting (q : ℤ) (f : Chart → ℂ) (x : Chart)
    (hx : x.2.1 ∈ Ioo (-1 : ℝ) 1)
    (hf : TwiceDifferentiable (fun p => f (x.1, p)) x.2) :
    oneExpression q f x =
      -Dr (Dr f) x - (2 / x.1 : ℝ) * Dr f x +
      (angularSquare ((q : ℝ) / 2) (fun p => f (x.1, p)) x.2 -
        (((q : ℝ) / 2) ^ 2 : ℝ) * f x) / (x.1 ^ 2 : ℝ) +
      (x.1 ^ 2 : ℝ) * f x := by
  rw [angularSquare_eq _ _ _ hx hf]
  simp [oneExpression]

end MagHK.MonopoleDifferential
