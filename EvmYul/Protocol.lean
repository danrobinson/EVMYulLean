namespace EvmYul

/--
Ethereum fork baseline represented by this semantics checkout.

This fork intentionally does not keep historical protocol variants alive: the
compiler-facing Ethereum baseline is Osaka.
-/
inductive EthereumFork where
  | osaka
  deriving BEq, DecidableEq, Inhabited, Repr

/--
Tempo protocol levels relevant to EVM execution/accounting.

`t6` is the active mainnet level at the time this profile was added; `t7` is
the latest documented Tempo level and adds storage credits plus dynamic-base-fee
accounting. Pre-T1C opcode behavior is intentionally excluded.
-/
inductive TempoFork where
  | t6
  | t7
  deriving BEq, DecidableEq, Inhabited, Repr

inductive Protocol where
  | ethereum (fork : EthereumFork)
  | tempo (fork : TempoFork)
  deriving BEq, DecidableEq, Repr

namespace Protocol

def osaka : Protocol :=
  .ethereum .osaka

def tempoT6 : Protocol :=
  .tempo .t6

def tempoLatest : Protocol :=
  .tempo .t7

instance : Inhabited Protocol :=
  ⟨osaka⟩

def isTempo : Protocol → Bool
  | .tempo _ => true
  | .ethereum _ => false

def nativeBalanceAlwaysZero (protocol : Protocol) : Bool :=
  protocol.isTempo

def callValueAlwaysZero (protocol : Protocol) : Bool :=
  protocol.isTempo

def nativeValueTransfersEnabled (protocol : Protocol) : Bool :=
  !protocol.isTempo

def sstoreSetGas : Protocol → Nat
  | .tempo _ => 250000
  | .ethereum .osaka => 20000

/--
Gas charged by CALL-style native-value transfer to an empty account.

Tempo has no native value transfer surface; its explicit account-creation charge
is modeled separately as `firstNonceAccountCreationGas`.
-/
def callNewAccountGas : Protocol → Nat
  | .tempo _ => 0
  | .ethereum .osaka => 25000

def firstNonceAccountCreationGas : Protocol → Nat
  | .tempo _ => 250000
  | .ethereum .osaka => 0

def createBaseGas : Protocol → Nat
  | .tempo _ => 500000
  | .ethereum .osaka => 32000

def codeDepositGasPerByte : Protocol → Nat
  | .tempo _ => 1000
  | .ethereum .osaka => 200

def txCreateGas : Protocol → Nat
  | .tempo _ => 500000
  | .ethereum .osaka => 32000

def initCodeWordGas : Protocol → Nat
  | .tempo _ => 0
  | .ethereum .osaka => 2

def eip7702AuthorizationBaseGas : Protocol → Nat
  | .tempo _ => 12500
  | .ethereum .osaka => 25000

def hasStorageCredits : Protocol → Bool
  | .tempo .t7 => true
  | _ => false

def hasDynamicBaseFee : Protocol → Bool
  | .tempo .t7 => true
  | _ => false

def tip20RewardsDeprecated : Protocol → Bool
  | .tempo .t7 => true
  | _ => false

def allOpcodesSupported (_protocol : Protocol) : Bool :=
  true

theorem osaka_not_tempo : osaka.isTempo = false := rfl

theorem tempoLatest_isTempo : tempoLatest.isTempo = true := rfl

theorem tempoLatest_sstoreSetGas :
    tempoLatest.sstoreSetGas = 250000 := rfl

theorem tempoLatest_createBaseGas :
    tempoLatest.createBaseGas = 500000 := rfl

theorem tempoLatest_codeDepositGasPerByte :
    tempoLatest.codeDepositGasPerByte = 1000 := rfl

theorem tempoLatest_hasStorageCredits :
    tempoLatest.hasStorageCredits = true := rfl

theorem tempoLatest_hasDynamicBaseFee :
    tempoLatest.hasDynamicBaseFee = true := rfl

end Protocol

end EvmYul
