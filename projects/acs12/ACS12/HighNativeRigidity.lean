import ACS12.HighSourceFloor
import ACS12.PressureSortedAdjacent
import ACS12.NativeFiniteMassReturn

/-! One original-source analytic core on the full closed band for every count at least two. -/
namespace ACS12.Configuration
open NativeCells Pressure CenteredCircle.AllN

theorem small_source_mass_ratio {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2≤n) (hn₃ : n≤3) (hp : 2≤p)
    (i j : Fin n) : F.mass i≤(7*p/2)*F.mass j := by
  let σ:=Tuple.sort F.phase
  let a:=σ.symm i
  let b:=σ.symm j
  have hPrice : p+1≤7*p/2 := by linarith only [hp]
  have hSame : 1≤7*p/2 := by linarith only [hp]
  by_cases hab : a=b
  · have hij : i=j:=by
      have h:=congrArg σ hab
      simpa only [a,b,Equiv.apply_symm_apply] using h
    subst j
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hSame (F.mass_pos i).le
  · have hOr : b.val=(a.val+1)%n ∨ a.val=(b.val+1)%n := by
      have ha:=a.isLt
      have hb:=b.isLt
      have hne : a.val≠b.val:=fun h=>hab (Fin.ext h)
      interval_cases n <;> omega
    have hRaw : F.mass (σ a)<(p+1)*F.mass (σ b) := by
      rcases hOr with h|h
      · exact (originalSorted_adjacent_ratio (by omega) (by linarith only [hp]) F a b h).1
      · exact (originalSorted_adjacent_ratio (by omega) (by linarith only [hp]) F b a h).2
    have hPay:=mul_le_mul_of_nonneg_right hPrice (F.mass_pos (σ b)).le
    have h:=hRaw.le.trans hPay
    simpa only [a,b,Equiv.apply_symm_apply] using h

theorem high_mass_ratio {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2≤n) (hp : 2≤p) (hP : p≤4) (i j : Fin n) :
    F.mass i≤(7*p/2)*F.mass j := by
  by_cases hFour : 4≤n
  · obtain ⟨C⟩:=F.exists_normalized_chart (by omega)
    have hFloor:=high_original_mass_floor hFour hp hP F C j i
    rw [C.mass_eq i,C.mass_eq j] at hFloor
    have hPrice:=(div_lt_iff₀ (by linarith only [hp] : 0<7*p)).mp hFloor
    have hRoot:=F.mass_pos C.source.root
    have hScale:=mul_lt_mul_of_pos_right hPrice hRoot
    have hLeft : (2*(F.mass i/F.mass C.source.root))*F.mass C.source.root=2*F.mass i := by
      field_simp [hRoot.ne']
    have hRight : ((F.mass j/F.mass C.source.root)*(7*p))*F.mass C.source.root=(7*p)*F.mass j := by
      field_simp [hRoot.ne']
    rw [hLeft,hRight] at hScale
    linarith only [hScale]
  · exact F.small_source_mass_ratio hn (by omega) hp i j

theorem rigidity_two_four_core {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 2 ≤ p) (hP : p ≤ 4) : IsEqualMassRegular F := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hn₂ : 2 ≤ n := by omega
  by_cases hne : ∃ i, relativeMass F.mass i ≠ 1
  · have hNative := nativeRootRow_gt_logRowMean hn hp hP F.mass_pos hne (F.high_mass_ratio hn hp hP)
    have hPhysical := (rootRow_le_commonRow hn₂ hp₀ F).trans (commonRow_le_logRowMean hn₂ hp₀ F)
    exact False.elim (not_lt_of_ge hPhysical hNative)
  · push Not at hne
    have hn₀ : 0 < n := by omega
    have hMean : 0 < meanMass F.mass :=
      div_pos (massTotal_pos hn₀ F.mass_pos) (Nat.cast_pos.mpr hn₀)
    let i₀ : Fin n := ⟨0,hn₀⟩
    have hEqual (i : Fin n) : F.mass i = meanMass F.mass := by
      have h := hne i
      change F.mass i / meanMass F.mass = 1 at h
      exact (div_eq_one_iff_eq hMean.ne').mp h
    apply F.equal_mass_regular hn₂ hp₀.le (F.mass_pos i₀)
    exact fun i => (hEqual i).trans (hEqual i₀).symm

theorem rigidity_two_four {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2≤n) (hp : 2≤p) (hP : p≤4) : IsEqualMassRegular F := by
  exact F.rigidity_two_four_core hn hp hP

end ACS12.Configuration
