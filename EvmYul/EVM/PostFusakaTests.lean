import EvmYul.EVM.Gas
import EvmYul.EVM.Instr
import EvmYul.Maps.AccountMap
import EvmYul.State.Account

namespace EvmYul

open Operation

private def delegationCode (targetBytes : ByteArray) : ByteArray :=
  ⟨#[0xef, 0x01, 0x00]⟩ ++ targetBytes

private def authority : AccountAddress := .ofNat 0x1000
private def target : AccountAddress := .ofNat 0x2000
private def targetAddressBytes : ByteArray :=
  ⟨#[0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x20, 0x00]⟩
private def expmodAddressBytes : ByteArray :=
  ⟨#[0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x05]⟩
private def targetCode : ByteArray := ⟨#[0x60, 0x01, 0x00]⟩

private def delegatedAccountMap : AccountMap .EVM :=
  (default : AccountMap .EVM)
    |>.insert authority { (default : Account .EVM) with code := delegationCode targetAddressBytes }
    |>.insert target { (default : Account .EVM) with code := targetCode }

private def delegatedToPrecompileAccountMap : AccountMap .EVM :=
  (default : AccountMap .EVM)
    |>.insert authority { (default : Account .EVM) with code := delegationCode expmodAddressBytes }

private def precompileWithDelegationBytesAccountMap : AccountMap .EVM :=
  (default : AccountMap .EVM)
    |>.insert 5 { (default : Account .EVM) with code := delegationCode targetAddressBytes }

private def createCostState (schedule : GasSchedule) : EVM.State :=
  { (default : EVM.State) with
      stack := [⟨0⟩, ⟨0⟩, ⟨32⟩]
      executionEnv :=
        { (default : ExecutionEnv .EVM) with
            gasSchedule := schedule } }

private def sstoreOwner : AccountAddress := .ofNat 0x3000

private def sstoreCleanCreateState (schedule : GasSchedule) : EVM.State :=
  { (default : EVM.State) with
      stack := [⟨1⟩, ⟨2⟩]
      accountMap :=
        (default : AccountMap .EVM).insert sstoreOwner
          (default : Account .EVM)
      executionEnv :=
        { (default : ExecutionEnv .EVM) with
            codeOwner := sstoreOwner
            gasSchedule := schedule } }

#guard UInt256.clz ⟨0⟩ == ⟨256⟩
#guard UInt256.clz ⟨1⟩ == ⟨255⟩
#guard UInt256.clz ⟨0x8000000000000000000000000000000000000000000000000000000000000000⟩ == ⟨0⟩
#guard EVM.parseInstr 0x1e == some (.CLZ : Operation .EVM)
#guard EVM.δ (.CLZ : Operation .EVM) == some 1
#guard EVM.α (.CLZ : Operation .EVM) == some 1
#guard EVM.C' (default : EVM.State) (.CLZ : Operation .EVM) == GasConstants.Glow
#guard EVM.selectedC' (createCostState GasSchedule.osaka) (.CREATE : Operation .EVM) == 32002
#guard EVM.selectedC' (createCostState GasSchedule.tempoLatest) (.CREATE : Operation .EVM) == 500000
#guard EVM.selectedC' (sstoreCleanCreateState GasSchedule.osaka) (.SSTORE : Operation .EVM) == 22100
#guard EVM.selectedC' (sstoreCleanCreateState GasSchedule.tempoLatest) (.SSTORE : Operation .EVM) == 252100

#guard eip7702DelegationTargetOfCode? (delegationCode targetAddressBytes) == some target
#guard eip7702DelegationTargetOfCode? targetCode == none

#guard
  match toExecute .EVM delegatedAccountMap authority with
  | .Code code => code == targetCode
  | .Precompiled _ => false

#guard
  match toExecute .EVM delegatedToPrecompileAccountMap authority with
  | .Code code => code == default
  | .Precompiled _ => false

#guard
  match toExecute .EVM precompileWithDelegationBytesAccountMap 5 with
  | .Precompiled .expmod => true
  | _ => false

#guard
  EVM.CdelegatedCodeAccess authority delegatedAccountMap (default : Substate) ==
    GasConstants.Gcoldaccountaccess

#guard
  EVM.CdelegatedCodeAccess authority delegatedAccountMap
      ((default : Substate).addAccessedAccount target) ==
    GasConstants.Gwarmaccess

end EvmYul
