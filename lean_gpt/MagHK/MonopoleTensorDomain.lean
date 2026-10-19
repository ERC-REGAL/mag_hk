import MagHK.MonopoleRealization

/-! Standard operator-domain inputs for angular separation. Both statements
are uniform in charge and in the angular modes. Their conclusions identify
actual L² operator images, and neither assumes an interacting eigenstate. -/
noncomputable section
namespace MagHK.MonopoleTensorDomain
open MeasureTheory
open MagHK.MonopoleRealization MagHK.MonopoleTrial

/-- Magnetic Hardy's bound makes Coulomb multiplication infinitesimally
operator bounded relative to the nonnegative oscillator. Kato–Rellich then
identifies the domains and the actual operator sum. -/
def StandardCoulombOperatorLibrary : Prop :=
  ∀ q (F₀ F : FermionSystem), FermionFacts F₀ q 0 → FermionFacts F q coulomb →
    ∀ ψ (hψ : ψ ∈ F.domain), ∃ h₀ : ψ ∈ F₀.domain,
      ∀ᵐ p ∂pairMeasure,
        ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState) p =
          ((F₀.map ⟨ψ, h₀⟩ : FermionState) : PairState) p +
            (coulomb p : ℂ) * (ψ : PairState) p

def angularWedge (Y Z : Angle → ℂ) (p : Angle × Angle) : ℂ :=
  MagHK.Slater.slaterSlice (Y p.1) (Z p.1) Y Z p.2

def radialWedge (f : ℝ → ℂ) (Y Z : Angle → ℂ) (p : Chart × Chart) : ℂ :=
  f p.1.1 * f p.2.1 * angularWedge Y Z (p.1.2, p.2.2)

/-- The domain theorem for a nonnegative radial tensor sum. The angular
operators have the same eigenvalue, so the two radial images are one and
the same function h. The usual spectral second-moment argument proves
that a normalized rank-one tensor in the sum domain has its factor in
the radial domain. The image formula is the tensor Leibniz rule. -/
def StandardSeparatedDomainLibrary : Prop :=
  ∀ q (F₀ : FermionSystem), FermionFacts F₀ q 0 → ∀ (lam : ℝ) (Y Z : Angle → ℂ),
    AngularSolution ((q : ℝ) / 2) lam Y → AngularSolution ((q : ℝ) / 2) lam Z →
    MagHK.Slater.OrthonormalPair sphereMeasure Y Z →
    ∀ (f : ℝ → ℂ) (c : ℂ),
      (∫ r, Complex.normSq (f r) ∂radialVolume) = 1 →
      ∀ ψ (hψ : ψ ∈ F₀.domain),
        (∀ᵐ p ∂pairMeasure, (ψ : PairState) p = c * radialWedge f Y Z p) →
        ∃ h : ℝ → ℂ, ∀ᵐ p ∂pairMeasure,
          ((F₀.map ⟨ψ, hψ⟩ : FermionState) : PairState) p =
            c * (h p.1.1 * f p.2.1 + f p.1.1 * h p.2.1) *
              angularWedge Y Z (p.1.2, p.2.2)

end MagHK.MonopoleTensorDomain
