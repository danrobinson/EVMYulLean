import EvmYul.EVM.Semantics

open EvmYul

namespace EvmYul.EVM.CallTouchSmoke

def source : AccountAddress := AccountAddress.ofNat 100
def recipient : AccountAddress := AccountAddress.ofNat 101

def accounts : AccountMap .EVM :=
  (default : AccountMap .EVM).insert source
    { (default : Account .EVM) with balance := UInt256.ofNat 1 }

example :
    EVM.thetaCallTransfer accounts source recipient (UInt256.ofNat 0) =
      accounts := by
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
  exact EVM.thetaCallTransfer_zero accounts source recipient

example :
    EVM.thetaCallTransfer accounts source source (UInt256.ofNat 1) = accounts := by
  simpa using EVM.thetaCallTransfer_self accounts source (UInt256.ofNat 1)

def run (code : ByteArray) :
    Except EVM.ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 ×
        Substate × Bool × ByteArray) :=
  EVM.Θ 8 [] default default default accounts accounts
    { totalGasUsedInBlock := 0, transactionReceipts := #[] } default
    source source recipient (.Code code) (UInt256.ofNat 100000)
    (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) default 1 default true

example :
    (match run default with
    | .ok (_, _, _, substate, success, _) =>
        success && substate.touchedAccounts.contains source &&
          substate.touchedAccounts.contains recipient
    | .error _ => false) = true := by
  native_decide

def exceptionalCode : ByteArray := ⟨#[0xfe]⟩

example :
    (match run exceptionalCode with
    | .ok (_, _, _, substate, success, _) =>
        !success && !substate.touchedAccounts.contains source &&
          !substate.touchedAccounts.contains recipient
    | .error _ => false) = true := by
  native_decide

end EvmYul.EVM.CallTouchSmoke
