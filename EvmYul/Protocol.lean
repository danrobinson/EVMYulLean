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

structure GasSchedule where
  sstoreSetGas : Nat
  callValueTransferGas : Nat
  callNewAccountGas : Nat
  firstNonceAccountCreationGas : Nat
  createBaseGas : Nat
  codeDepositGasPerByte : Nat
  txCreateGas : Nat
  initCodeWordGas : Nat
  eip7702AuthorizationBaseGas : Nat
  deriving BEq, DecidableEq, Repr

namespace GasSchedule

def osaka : GasSchedule :=
  { sstoreSetGas := 20000
    callValueTransferGas := 9000
    callNewAccountGas := 25000
    firstNonceAccountCreationGas := 0
    createBaseGas := 32000
    codeDepositGasPerByte := 200
    txCreateGas := 32000
    initCodeWordGas := 2
    eip7702AuthorizationBaseGas := 25000 }

def tempo : GasSchedule :=
  { sstoreSetGas := 250000
    callValueTransferGas := 0
    callNewAccountGas := 0
    firstNonceAccountCreationGas := 250000
    createBaseGas := 500000
    codeDepositGasPerByte := 1000
    txCreateGas := 500000
    initCodeWordGas := 0
    eip7702AuthorizationBaseGas := 12500 }

def tempoLatest : GasSchedule :=
  tempo

instance : Inhabited GasSchedule :=
  ⟨osaka⟩

theorem tempoLatest_sstoreSetGas :
    tempoLatest.sstoreSetGas = 250000 := rfl

theorem tempoLatest_createBaseGas :
    tempoLatest.createBaseGas = 500000 := rfl

theorem tempoLatest_codeDepositGasPerByte :
    tempoLatest.codeDepositGasPerByte = 1000 := rfl

end GasSchedule

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

def gasSchedule : Protocol → GasSchedule
  | .tempo _ => GasSchedule.tempo
  | .ethereum .osaka => GasSchedule.osaka

def sstoreSetGas : Protocol → Nat
  | protocol => protocol.gasSchedule.sstoreSetGas

/--
Gas charged by CALL-style native-value transfer to an empty account.

Tempo has no native value transfer surface; its explicit account-creation charge
is modeled separately as `firstNonceAccountCreationGas`.
-/
def callNewAccountGas : Protocol → Nat
  | protocol => protocol.gasSchedule.callNewAccountGas

def firstNonceAccountCreationGas : Protocol → Nat
  | protocol => protocol.gasSchedule.firstNonceAccountCreationGas

def createBaseGas : Protocol → Nat
  | protocol => protocol.gasSchedule.createBaseGas

def codeDepositGasPerByte : Protocol → Nat
  | protocol => protocol.gasSchedule.codeDepositGasPerByte

def txCreateGas : Protocol → Nat
  | protocol => protocol.gasSchedule.txCreateGas

def initCodeWordGas : Protocol → Nat
  | protocol => protocol.gasSchedule.initCodeWordGas

def eip7702AuthorizationBaseGas : Protocol → Nat
  | protocol => protocol.gasSchedule.eip7702AuthorizationBaseGas

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
