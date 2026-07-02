namespace EvmYul

universe u

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

/--
Open gas/accounting policy interface.

The policy is parameterized by the state type it observes.  Osaka and current
Tempo profiles below are constant policies, but callers can instantiate this
record with a richer state carrying private accounting metadata and make any
gas component depend on that state.
-/
structure GasPolicy (State : Type u) where
  sstoreSetGas : State → Nat
  callValueTransferGas : State → Nat
  callNewAccountGas : State → Nat
  firstNonceAccountCreationGas : State → Nat
  createBaseGas : State → Nat
  codeDepositGasPerByte : State → Nat
  txCreateGas : State → Nat
  initCodeWordGas : State → Nat
  eip7702AuthorizationBaseGas : State → Nat
  hasStorageCredits : State → Bool := fun _ => false
  hasDynamicBaseFee : State → Bool := fun _ => false
  tip20RewardsDeprecated : State → Bool := fun _ => false

namespace GasPolicy

def osaka {State : Type u} : GasPolicy State where
  sstoreSetGas := fun _ => 20000
  callValueTransferGas := fun _ => 9000
  callNewAccountGas := fun _ => 25000
  firstNonceAccountCreationGas := fun _ => 0
  createBaseGas := fun _ => 32000
  codeDepositGasPerByte := fun _ => 200
  txCreateGas := fun _ => 32000
  initCodeWordGas := fun _ => 2
  eip7702AuthorizationBaseGas := fun _ => 25000
  hasStorageCredits := fun _ => false
  hasDynamicBaseFee := fun _ => false
  tip20RewardsDeprecated := fun _ => false

def tempoT6 {State : Type u} : GasPolicy State where
  sstoreSetGas := fun _ => 250000
  callValueTransferGas := fun _ => 0
  callNewAccountGas := fun _ => 0
  firstNonceAccountCreationGas := fun _ => 250000
  createBaseGas := fun _ => 500000
  codeDepositGasPerByte := fun _ => 1000
  txCreateGas := fun _ => 500000
  initCodeWordGas := fun _ => 0
  eip7702AuthorizationBaseGas := fun _ => 12500
  hasStorageCredits := fun _ => false
  hasDynamicBaseFee := fun _ => false
  tip20RewardsDeprecated := fun _ => false

def tempoLatest {State : Type u} : GasPolicy State where
  sstoreSetGas := fun _ => 250000
  callValueTransferGas := fun _ => 0
  callNewAccountGas := fun _ => 0
  firstNonceAccountCreationGas := fun _ => 250000
  createBaseGas := fun _ => 500000
  codeDepositGasPerByte := fun _ => 1000
  txCreateGas := fun _ => 500000
  initCodeWordGas := fun _ => 0
  eip7702AuthorizationBaseGas := fun _ => 12500
  hasStorageCredits := fun _ => true
  hasDynamicBaseFee := fun _ => true
  tip20RewardsDeprecated := fun _ => true

end GasPolicy

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

def gasPolicy {State : Type u} : Protocol → GasPolicy State
  | .ethereum .osaka => GasPolicy.osaka
  | .tempo .t6 => GasPolicy.tempoT6
  | .tempo .t7 => GasPolicy.tempoLatest

def sstoreSetGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).sstoreSetGas state

def sstoreSetGas (protocol : Protocol) : Nat :=
  protocol.sstoreSetGasFor ()

def callValueTransferGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).callValueTransferGas state

def callValueTransferGas (protocol : Protocol) : Nat :=
  protocol.callValueTransferGasFor ()

/--
Gas charged by CALL-style native-value transfer to an empty account.

Tempo has no native value transfer surface; its explicit account-creation charge
is modeled separately as `firstNonceAccountCreationGas`.
-/
def callNewAccountGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).callNewAccountGas state

def callNewAccountGas (protocol : Protocol) : Nat :=
  protocol.callNewAccountGasFor ()

def firstNonceAccountCreationGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).firstNonceAccountCreationGas state

def firstNonceAccountCreationGas (protocol : Protocol) : Nat :=
  protocol.firstNonceAccountCreationGasFor ()

def createBaseGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).createBaseGas state

def createBaseGas (protocol : Protocol) : Nat :=
  protocol.createBaseGasFor ()

def codeDepositGasPerByteFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).codeDepositGasPerByte state

def codeDepositGasPerByte (protocol : Protocol) : Nat :=
  protocol.codeDepositGasPerByteFor ()

def txCreateGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).txCreateGas state

def txCreateGas (protocol : Protocol) : Nat :=
  protocol.txCreateGasFor ()

def initCodeWordGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).initCodeWordGas state

def initCodeWordGas (protocol : Protocol) : Nat :=
  protocol.initCodeWordGasFor ()

def eip7702AuthorizationBaseGasFor {State : Type u} (protocol : Protocol)
    (state : State) : Nat :=
  (protocol.gasPolicy).eip7702AuthorizationBaseGas state

def eip7702AuthorizationBaseGas (protocol : Protocol) : Nat :=
  protocol.eip7702AuthorizationBaseGasFor ()

def hasStorageCreditsFor {State : Type u} (protocol : Protocol)
    (state : State) : Bool :=
  (protocol.gasPolicy).hasStorageCredits state

def hasStorageCredits (protocol : Protocol) : Bool :=
  protocol.hasStorageCreditsFor ()

def hasDynamicBaseFeeFor {State : Type u} (protocol : Protocol)
    (state : State) : Bool :=
  (protocol.gasPolicy).hasDynamicBaseFee state

def hasDynamicBaseFee (protocol : Protocol) : Bool :=
  protocol.hasDynamicBaseFeeFor ()

def tip20RewardsDeprecatedFor {State : Type u} (protocol : Protocol)
    (state : State) : Bool :=
  (protocol.gasPolicy).tip20RewardsDeprecated state

def tip20RewardsDeprecated (protocol : Protocol) : Bool :=
  protocol.tip20RewardsDeprecatedFor ()

def allOpcodesSupported (_protocol : Protocol) : Bool :=
  true

@[simp] theorem sstoreSetGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.sstoreSetGasFor state = protocol.sstoreSetGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem callValueTransferGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.callValueTransferGasFor state =
      protocol.callValueTransferGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem callNewAccountGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.callNewAccountGasFor state =
      protocol.callNewAccountGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem firstNonceAccountCreationGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.firstNonceAccountCreationGasFor state =
      protocol.firstNonceAccountCreationGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem createBaseGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.createBaseGasFor state = protocol.createBaseGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem codeDepositGasPerByteFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.codeDepositGasPerByteFor state =
      protocol.codeDepositGasPerByte := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem txCreateGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.txCreateGasFor state = protocol.txCreateGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem initCodeWordGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.initCodeWordGasFor state = protocol.initCodeWordGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem eip7702AuthorizationBaseGasFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.eip7702AuthorizationBaseGasFor state =
      protocol.eip7702AuthorizationBaseGas := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem hasStorageCreditsFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.hasStorageCreditsFor state = protocol.hasStorageCredits := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem hasDynamicBaseFeeFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.hasDynamicBaseFeeFor state = protocol.hasDynamicBaseFee := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

@[simp] theorem tip20RewardsDeprecatedFor_eq {State : Type u}
    (protocol : Protocol) (state : State) :
    protocol.tip20RewardsDeprecatedFor state =
      protocol.tip20RewardsDeprecated := by
  cases protocol with
  | ethereum fork => cases fork <;> rfl
  | tempo fork => cases fork <;> rfl

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

theorem osaka_gasPolicy {State : Type u} :
    Protocol.gasPolicy (State := State) osaka = GasPolicy.osaka := rfl

theorem tempoLatest_gasPolicy {State : Type u} :
    Protocol.gasPolicy (State := State) tempoLatest =
      GasPolicy.tempoLatest := rfl

theorem osaka_gasPolicy_sstoreSetGas {State : Type u} (state : State) :
    (Protocol.gasPolicy (State := State) osaka).sstoreSetGas state =
      20000 := rfl

theorem tempoLatest_gasPolicy_sstoreSetGas {State : Type u} (state : State) :
    (Protocol.gasPolicy (State := State) tempoLatest).sstoreSetGas state =
      250000 := rfl

end Protocol

end EvmYul
