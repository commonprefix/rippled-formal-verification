import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Witness data for the `*_dilution_attained` sharpness theorems

The concrete lawful vault and the operations that strictly decrease per-share
value, backing the `*_dilution_attained` headlines in `Dilution.lean`. The
starting state `baseV` is the one the differential search
(`scripts/DilutionSearch.lean`) produces through the public API (an IOU vault at
scale `6`, seed deposit `899999999.876543`, donation `123.4567891`), reproduced
here as a record literal so the run and the strict-decrease inequality are closed
by `native_decide` on the fully concrete decision procedures.

`native_decide` compiles the decidable propositions to native code and trusts the
result through the `Lean.ofReduceBool` axiom. The mechanism suits the sharpness
witnesses: the search already exhibited a concrete diluting vector for each
operation, so the only content is confirming, by running the model, that the
vector diverges from the `1 - depositε` guarantee. Kernel-checked universal
proofs (the `*_no_dilution` bounds) never use it.

The `Decidable` instances for the vault predicates (`Vault.WF`, `Vault.Valid`,
`Vault.Lawful`, and the `STAmount` canonical shapes) are the ones the untrusted
boundary check `Vault.validate` was left to await; they are derivable because every
clause is a decidable arithmetic or storage-shape condition, and the `assetsMaximum`
quantifier ranges over an `Option` (here always `none`). -/

-- `native_decide` is the approved mechanism for these sharpness witnesses (it trusts the
-- compiler through `Lean.ofReduceBool`); the universal `*_no_dilution` bounds never use it.
set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Decidable instances for the concrete none-cap witness states -/

/-- `Number.isnormal` is a decidable arithmetic condition. -/
instance Number.instDecidableIsnormal (n : Number) : Decidable n.isnormal := by
  unfold Number.isnormal; infer_instance

/-- A bounded quantifier over an `Option` is decidable when its body is. -/
instance instDecidableBallOption {α} (o : Option α) (P : α → Prop) [DecidablePred P] :
    Decidable (∀ m ∈ o, P m) :=
  match o with
  | none => isTrue (fun m hm => absurd hm (by simp))
  | some a => decidable_of_iff (P a) (by simp [Option.mem_def])

instance STAmount.instDecidableIntegralCanonical (s : STAmount) : Decidable s.IntegralCanonical :=
  decidable_of_iff
    (s.mNumericType.isIntegral = true ∧ s.mOffset = 0 ∧
      s.mValue.toNat ≤ s.mNumericType.maxValue.toNat)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

instance STAmount.instDecidableIOUCanonical (s : STAmount) : Decidable s.IOUCanonical :=
  decidable_of_iff
    (s.mNumericType = .fractional ∧ 10 ^ 15 ≤ s.mValue.toNat ∧ s.mValue.toNat < 10 ^ 16 ∧
      (-96 : ℤ) ≤ s.mOffset ∧ s.mOffset ≤ 80)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

instance STAmount.instDecidableCanonical (s : STAmount) : Decidable s.Canonical := by
  unfold STAmount.Canonical; infer_instance

instance STAmount.instDecidableExactCanonical (s : STAmount) : Decidable s.ExactCanonical := by
  unfold STAmount.ExactCanonical; infer_instance

instance Vault.instDecidableWF (v : Vault) : Decidable v.WF :=
  decidable_of_iff
    (v.assetsTotal.isNormalized ∧ v.assetsAvailable.isNormalized ∧
     (∀ m ∈ v.assetsMaximum, m.isNormalized) ∧ v.sharesTotal.isNormalized ∧
     v.lossUnrealized.isNormalized ∧
     0 ≤ v.sharesTotal.toRat ∧ v.sharesTotal.toRat.den = 1 ∧
     (v.numericType.isIntegral = true → v.scale = 0) ∧ v.scale.toNat ≤ 18)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

instance Vault.instDecidableValid (v : Vault) : Decidable v.Valid :=
  decidable_of_iff
    (0 ≤ v.assetsTotal.toRat ∧ 0 ≤ v.assetsAvailable.toRat ∧
     v.assetsAvailable.toRat ≤ v.assetsTotal.toRat ∧
     (∀ m ∈ v.assetsMaximum, 0 < m.toRat) ∧
     (v.sharesTotal.toRat = 0 → v.assetsTotal.toRat = 0 ∧ v.assetsAvailable.toRat = 0) ∧
     (∀ m ∈ v.assetsMaximum, v.assetsTotal.toRat ≤ m.toRat) ∧
     0 ≤ v.lossUnrealized.toRat ∧
     v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat ∧
     0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

instance Vault.instDecidableLawful (v : Vault) : Decidable v.Lawful :=
  decidable_of_iff (v.WF ∧ v.Valid) ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-! ## The base witness vault, amounts, and results -/

/-- The lawful IOU vault the search reaches through the public API:
`assetsTotal = assetsAvailable = 900000123.3333321`, `sharesTotal = 899999999876543`,
nothing unrealized or reserved, no cap, scale `6`. -/
def baseV : Vault :=
  { assetsTotal := ⟨false, 9000001233333321000, -10⟩
  , assetsAvailable := ⟨false, 9000001233333321000, -10⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 6
  , sharesTotal := ⟨false, 8999999998765430000, -4⟩
  , lossUnrealized := Number.zero }

/-- Witness deposit amount `1587.0335`: the stored-total update rounds against the
vault by more than the charge's upward surplus. -/
def depAmt : STAmount := STAmount.unchecked .fractional 1587033500000000 (-12) false

/-- Witness clawback amount `1000.917`. -/
def clawAmt : STAmount := STAmount.unchecked .fractional 1000917000000000 (-12) false

/-- Witness holder-shares balance passed to `Vault.clawback`. Unused on this
run since `clawAmt` is nonzero (the zero-amount "claw all" branch never fires). -/
def clawHolderShares : STAmount := STAmount.zero .int64

/-- Witness withdrawal share count `1003103695`. -/
def shAmt : STAmount := STAmount.unchecked .int64 1003103695 0 false

/-- The deposit result. `getD` never fires (the run succeeds); the fallback keeps
the definition total. -/
def depR : DepositResult :=
  (baseV.deposit depAmt false).toOption.getD (DepositResult.rejected baseV .tecINTERNAL)

/-- The withdrawal result. -/
def wdR : WithdrawResult :=
  (baseV.withdraw (.vaultShares shAmt) false).toOption.getD (WithdrawResult.rejected baseV .tecINTERNAL)

/-- The clawback result. -/
def clawR : ClawbackResult :=
  (baseV.clawback clawAmt clawHolderShares).toOption.getD (ClawbackResult.rejected baseV .tecINTERNAL)

/-- Zero clawed amount for the claw all dilution run. -/
def clawA0 : STAmount := STAmount.zero .fractional

/-- Holder balance of the zero amount run. -/
def clawZeroShares : STAmount := clawR.sharesDestroyed

/-- The zero amount clawback result. -/
def clawR0 : ClawbackResult :=
  (baseV.clawback clawA0 clawZeroShares).toOption.getD (ClawbackResult.rejected baseV .tecINTERNAL)

/-- Second deposit in the compounding history: the first deposit takes `baseV` to
`depR.vault'`, this one takes it one step further. -/
def r2 : DepositResult :=
  (depR.vault'.deposit depAmt false).toOption.getD (DepositResult.rejected baseV .tecINTERNAL)

/-- The base witness vault is lawful.

`native_decide` (`Lean.ofReduceBool`): a fully concrete decidable check. -/
theorem baseV_lawful : baseV.Lawful := by native_decide

/-! ## The diluting operations, established by native evaluation

Each lemma bundles one operation's success, its `error = none` exit, and the
strict per-share decrease against `baseV` in cross-multiplied form. -/

/-- The deposit succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem depR_dilutes :
    0 < depAmt.toRat ∧ baseV.deposit depAmt false = .ok depR ∧ depR.error = none ∧
    depR.vault'.withdrawNav * baseV.sharesTotal.toRat <
      baseV.withdrawNav * depR.vault'.sharesTotal.toRat := by native_decide

/-- The withdrawal succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem wdR_dilutes :
    baseV.withdraw (.vaultShares shAmt) false = .ok wdR ∧ wdR.error = none ∧
    wdR.vault'.withdrawNav * baseV.sharesTotal.toRat <
      baseV.withdrawNav * wdR.vault'.sharesTotal.toRat := by native_decide

/-- The clawback succeeds and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem clawR_dilutes :
    baseV.clawback clawAmt clawHolderShares = .ok clawR ∧ clawR.error = none ∧
    clawR.vault'.withdrawNav * baseV.sharesTotal.toRat <
      baseV.withdrawNav * clawR.vault'.sharesTotal.toRat := by native_decide

/-- The zero-amount clawback destroys exactly the holder's balance (a canonical
nonnegative integral amount) and strictly decreases per-share value.

`native_decide` (`Lean.ofReduceBool`). -/
theorem clawR0_dilutes :
    clawA0.isZero = true ∧
    clawZeroShares.IntegralCanonical ∧ clawZeroShares.Canonical ∧
    clawZeroShares.negative = false ∧
    baseV.clawback clawA0 clawZeroShares = .ok clawR0 ∧ clawR0.error = none ∧
    clawR0.sharesDestroyed = clawZeroShares ∧
    clawR0.vault'.withdrawNav * baseV.sharesTotal.toRat <
      baseV.withdrawNav * clawR0.vault'.sharesTotal.toRat := by native_decide

/-- The two-deposit history: each step satisfies its `ReachableFromIn.deposit`
side conditions (canonical storage, positive amount and shares, share domain), and
the endpoint `r2.vault'` strictly dilutes against `baseV`. Bundled so the
`ReachableFromIn` assembly in `Dilution.lean` reuses one native run.

`native_decide` (`Lean.ofReduceBool`). -/
theorem reachable_chain_facts :
    (baseV.deposit depAmt false = .ok depR ∧ depAmt.Canonical ∧ 0 < depAmt.toRat ∧
      depR.amountDeposit'.ExactCanonical ∧ 0 ≤ depR.amountDeposit'.toRat ∧
      depR.sharesIssued.IntegralCanonical ∧ 0 ≤ depR.sharesIssued.toRat ∧
      baseV.sharesTotal.toRat + depR.sharesIssued.toRat ≤ 2 ^ 63 - 1) ∧
    (depR.vault'.deposit depAmt false = .ok r2 ∧ depAmt.Canonical ∧ 0 < depAmt.toRat ∧
      r2.amountDeposit'.ExactCanonical ∧ 0 ≤ r2.amountDeposit'.toRat ∧
      r2.sharesIssued.IntegralCanonical ∧ 0 ≤ r2.sharesIssued.toRat ∧
      depR.vault'.sharesTotal.toRat + r2.sharesIssued.toRat ≤ 2 ^ 63 - 1) ∧
    (r2.vault'.withdrawNav * baseV.sharesTotal.toRat <
      baseV.withdrawNav * r2.vault'.sharesTotal.toRat) := by native_decide

/-! ## The `*_witness` existentials the headlines delegate to -/

theorem deposit_dilution_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (r : DepositResult),
      v.Lawful ∧ 0 < amountDeposit.toRat ∧
      v.deposit amountDeposit false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  ⟨baseV, depAmt, depR, baseV_lawful, depR_dilutes.1, depR_dilutes.2.1, depR_dilutes.2.2.1,
    depR_dilutes.2.2.2⟩

theorem withdraw_dilution_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult),
      v.Lawful ∧ v.withdraw amount false = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  ⟨baseV, .vaultShares shAmt, wdR, baseV_lawful, wdR_dilutes.1, wdR_dilutes.2.1, wdR_dilutes.2.2⟩

theorem clawback_dilution_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.Lawful ∧ v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  ⟨baseV, clawAmt, clawHolderShares, clawR, baseV_lawful, clawR_dilutes.1, clawR_dilutes.2.1,
    clawR_dilutes.2.2⟩

theorem clawback_zero_dilution_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult),
      v.Lawful ∧ assets.isZero = true ∧
      holderShares.IntegralCanonical ∧ holderShares.Canonical ∧
      holderShares.negative = false ∧
      v.clawback assets holderShares = .ok r ∧ r.error = none ∧
      r.sharesDestroyed = holderShares ∧
      r.vault'.withdrawNav * v.sharesTotal.toRat <
        v.withdrawNav * r.vault'.sharesTotal.toRat :=
  ⟨baseV, clawA0, clawZeroShares, clawR0, baseV_lawful, clawR0_dilutes⟩

/-- Witness backing `ReachableFromIn.dilution_attained`: the two-deposit history
from `baseV` whose endpoint `r2.vault'` strictly dilutes against `baseV`. Each
`.deposit` step's `hcnz` sub-witness is a `by native_decide` (`Lean.ofReduceBool`)
on the concrete run. -/
theorem dilution_attained_witness :
    ∃ (w u : Vault) (n : ℕ),
      w.Lawful ∧ 1 < n ∧ Vault.ReachableFromIn w u n ∧
      u.withdrawNav * w.sharesTotal.toRat <
        w.withdrawNav * u.sharesTotal.toRat := by
  obtain ⟨⟨h1run, h1can, h1pos, -, -, -, -, h1sz⟩,
         ⟨h2run, h2can, h2pos, -, -, -, -, h2sz⟩, hdil⟩ := reachable_chain_facts
  refine ⟨baseV, r2.vault', 2, baseV_lawful, by norm_num, ?_, hdil⟩
  have s0 : Vault.ReachableFromIn baseV baseV 0 := .refl baseV
  have s1 : Vault.ReachableFromIn baseV depR.vault' 1 :=
    .deposit baseV baseV 0 depAmt false depR s0 h1run h1can h1pos (by native_decide) h1sz
  exact .deposit baseV depR.vault' 1 depAmt false r2 s1 h2run h2can h2pos (by native_decide) h2sz

end XRPL.Model.SingleAssetVault
