import ACS12.GammaTotalExponential
import ACS12.BoseNoiseExponential

/-! The same actual joint energy has a genuine positive exponential moment and every finite nonnegative power. -/
namespace ACS12.NativeCells
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem nativeJoint_exponential_moment {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    ∃ c > 0, Integrable (fun s => Real.exp (c*nativeJointEnergy z s)) (nativeJointMeasure p) := by
  let r := GammaMixture.gammaRate 0
  let c := r/(2*(z+1))
  have hr : 0 < r := GammaMixture.gammaRate_pos 0
  have hc : 0 < c := by unfold c; positivity
  have hcz : 0 ≤ c*z := mul_nonneg hc.le hz
  have hEq : c*(z+1) = r/2 := by unfold c; field_simp [show z+1≠0 by positivity]
  have hcR : c < r := by nlinarith only [hEq,hcz,hr]
  have hczR : c*z < r := by nlinarith only [hEq,hc,hr]
  have hX := GammaMixture.gammaTotal_exponential_integrable hp hc.le hcR
  have hχ := boseNoise_exponential_integrable hcz hczR
  have hProd := hX.smul_prod hχ
  refine ⟨c,hc,?_⟩
  convert hProd using 1
  funext s
  change Real.exp (c*(GammaMixture.gammaTotal s.1+z*boseNoise s.2)) =
    Real.exp (c*GammaMixture.gammaTotal s.1)*Real.exp ((c*z)*boseNoise s.2)
  rw [←Real.exp_add]
  congr 1
  ring

theorem nativeJoint_all_positive_moments {p z q : ℝ} (hp : 0 < p) (hz : 0 ≤ z) (hq : 0 ≤ q) :
    Integrable (fun s => nativeJointEnergy z s^q) (nativeJointMeasure p) := by
  letI := nativeJoint_probability hp
  obtain ⟨c,hc,hExp⟩ := nativeJoint_exponential_moment hp hz
  exact ACS12.integrable_rpow_of_exponential (measurable_nativeJointEnergy z)
    ((nativeJointEnergy_ae_pos hp hz).mono fun _ hs => hs.le) hc hExp hq

end ACS12.NativeCells
