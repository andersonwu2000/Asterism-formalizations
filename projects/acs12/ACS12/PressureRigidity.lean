import ACS12.PressureWeightedRigidity
import ACS12.PressurePhysicalSupport
import ACS12.FourSiteExchange
import ACS12.ShortCycle

/-! The original force equations on the half-open pressure band. -/
namespace ACS12.Configuration

theorem rigidity_pressure {n : ℕ} {p : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p < 2) (hn : 2 ≤ n)
    (F : Configuration n p) : IsEqualMassRegular F := by
  have hp₀ : 0 < p := by linarith only [hp]
  by_cases h₂ : n = 2
  · subst n
    exact F.two_sites_regular hp₀.le
  by_cases h₃ : n = 3
  · subst n
    exact F.three_sites_regular hp₀.le
  by_cases h₄ : n = 4
  · subst n
    exact F.four_sites_regular hp₀
  have hn₃ : 3 ≤ n := by omega
  obtain ⟨s,hs,hFloor,hCap,_⟩ := Pressure.normalizedPressureSource hp hp₂.le hn₃ F
  exact (F.scaleMass_regular_iff hs).mp
    (Pressure.weightedPressure_normalized_regular hp hp₂.le hn (F.scaleMass s hs)
      (fun i => (hFloor i).le) hCap)

end ACS12.Configuration
