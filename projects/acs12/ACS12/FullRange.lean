import ACS12.LowRigidity
import ACS12.MiddleRigidity
import ACS12.PressureRigidity
import ACS12.HighNativeRigidity
import ACS12.QuarticRigidity

/-! Full ACS12 for every nonnegative real exponent and every finite count at least two. -/
namespace ACS12

/-- The full original physical centered-cocircular force equations force equal masses
and a regular polygon for every nonnegative real exponent. -/
theorem Configuration.rigidity {n : ℕ} {α : ℝ} (F : Configuration n α)
    (hn : 2 ≤ n) (hα : 0 ≤ α) : IsEqualMassRegular F := by
  by_cases hZero : α = 0
  · subst α
    exact logarithmic hn F
  · have hPositive : 0 < α := lt_of_le_of_ne hα (Ne.symm hZero)
    by_cases hLow : α ≤ 1
    · exact F.rigidity_low hn hPositive hLow
    · by_cases hMiddle : α ≤ 9 / 5
      · exact F.rigidity_middle hn (le_of_not_ge hLow) hMiddle
      · by_cases hPressure : α < 2
        · exact F.rigidity_pressure (le_of_not_ge hMiddle) hPressure hn
        · by_cases hFour : α < 4
          · exact F.rigidity_two_four hn (le_of_not_gt hPressure) hFour.le
          · exact F.rigidity_atLeastFour hn (le_of_not_gt hFour)

end ACS12
