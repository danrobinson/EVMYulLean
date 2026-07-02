import EvmYul.EVM.Gas
import EvmYul.EVM.Instr
import EvmYul.EVM.Semantics
import EvmYul.Maps.AccountMap
import EvmYul.State.Account

namespace EvmYul

open Operation

private def bytes (xs : List UInt8) : ByteArray := List.toByteArray xs

private def wordBEByte (b : UInt8) : ByteArray :=
  bytes (List.replicate 31 0 ++ [b])

private def truncatedPush2Code : ByteArray := bytes [0x61, 0xab]

private def modexpWideBaseCalldata : ByteArray :=
  wordBEByte 33 ++ wordBEByte 1 ++ wordBEByte 2 ++
    bytes ([1] ++ List.replicate 32 0 ++ [1, 1, 1])

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

#guard UInt256.clz ⟨0⟩ == ⟨256⟩
#guard UInt256.clz ⟨1⟩ == ⟨255⟩
#guard UInt256.clz ⟨0x8000000000000000000000000000000000000000000000000000000000000000⟩ == ⟨0⟩
#guard EVM.parseInstr 0x1e == some (.CLZ : Operation .EVM)
#guard EVM.δ (.CLZ : Operation .EVM) == some 1
#guard EVM.α (.CLZ : Operation .EVM) == some 1
#guard EVM.C' (default : EVM.State) (.CLZ : Operation .EVM) == GasConstants.Glow

#guard
  match EVM.decode truncatedPush2Code (UInt256.ofNat 0) with
  | some (.PUSH2, some (value, 2)) => value == UInt256.ofNat 0xab00
  | _ => false

#guard
  let base := nat_of_slice modexpWideBaseCalldata 96 33
  let exp := nat_of_slice modexpWideBaseCalldata (96 + 33) 1
  let modulus := nat_of_slice modexpWideBaseCalldata (96 + 33 + 1) 2
  expMod modulus base exp == 1

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
