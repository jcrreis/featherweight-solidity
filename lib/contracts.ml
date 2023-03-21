open Types

(*
let bank_contract () : contract_def =
  let fb = {
    name = "fb";
    rettype = Unit;
    args = [];
    body = Return(Val(VUnit));
  } in

  let deposit = {
    name = "deposit";
    rettype = Unit;
    args = [];
    body = Return(
        (StateAssign(
            This None,
            "balances",
            MapWrite(
              StateRead(This None,"balances"), MsgSender, AritOp((Plus(MapRead(StateRead(This None,"balances"),MsgSender), MsgValue)))))))
  } in
  let getBalance = {
    name = "getBalance";
    rettype = UInt;
    args = [];
    body = MapRead(StateRead(This None,"balances"),MsgSender)
  } in
  let transfer = {
    name = "transfer";
    rettype = Unit;
    args = [(Address, "to"); (UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
              Seq(StateAssign(This None, "balances", MapWrite(
                  StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
                  StateAssign(This None, "balances", MapWrite(
                      StateRead(This None,"balances"), Var("to"), AritOp(Minus(MapRead(StateRead(This None,"balances"),Var("to")), Var("amount")))))
                ),
              Val(VUnit))
  } in
  let withdraw = {
    name = "withdraw";
    rettype = Unit;
    args = [(UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
              Seq(
                StateAssign(This None, "balances", MapWrite(
                    StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
                Transfer(MsgSender, Var("x"))
              ),
              Val(VUnit)
             )
  } in
  {
    name = "Bank";
    state = [(Map(Address, UInt),"balances")];
    constructor = ([(Map(Address, UInt),"balances")], (StateAssign(This None, "balances", Var("balances"))));
    functions = [fb;deposit; getBalance; transfer; withdraw];
  }


let blood_bank_contract () : contract_def =
  let setHealth = {
    name = "setHealth";
    rettype = Unit;
    args = [(Address, "donor"); (Bool, "isHealty")];
    body = Return (
        If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
           (StateAssign(
               This None,
               "healty",
               MapWrite(
                 StateRead(This None,"healty"), Var("donor"), Var("isHealty")))),
           Revert
          )
      );
  } in
  let isHealty = {
    name = "isHealty";
    rettype = Bool;
    args = [(Address, "donor")];
    body = Return(
        If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
           MapRead(StateRead(This None, "healty"), Var("donor")),
           Revert
          )
      );
  } in
  (* If(BoolOp(Conj(MapRead(StateRead(This None, "healty"), MsgSender), BoolOp(Conj(
            BoolOp(Greater(Var("donorBlood"),Val(VUInt(3000)))), BoolOp(Greater(
                AritOp(Minus(Var("donorBlood"), Var("amount"))), Val(VUInt(0)))))))),
          Seq(StateAssign(This None, "blood", AritOp(Plus(StateRead(This None, "blood"), Var("amount")))),Val(VBool(True))),
          Val(VBool(False))) *)
  let donate = {
    (* |Call of expr * string * expr * expr list e.f.value(e)(le) *)
    name = "donate";
    rettype = Bool;
    args = [(UInt, "amount")];
    body = Return(
        Let(UInt, "donorBlood",Call(Cons("Donor", MsgSender),"getBlood",Val(VUInt(0)),[]),
            Seq(StateAssign(This None, "blood", AritOp(Plus(StateRead(This None, "blood"), Var("amount")))),Val(VBool(True)))))
    ;
  } in
  let getDoctor = {
    name = "getDoctor";
    rettype = Address;
    args = [];
    body = Return(StateRead(This None, "doctor"));
  } in
  let getBlood = {
    name = "getBlood";
    rettype = UInt;
    args = [];
    body = Return(StateRead(This None, "blood"));
  } in
  {
    name = "BloodBank";
    state = [(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")];
    constructor = ([(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")],
                   (Seq((StateAssign(This None, "healty", Var("healty")),
                         Seq((StateAssign(This None, "doctor", Var("doctor"))),
                             StateAssign(This None, "blood", Var("blood")))))));

    (* constructor = ([], Val(VUnit));           *)
    functions = [setHealth; isHealty; donate; getDoctor; getBlood];
  }

let donor_contract () : contract_def =
  let donate = {
    name = "donate";
    rettype = Unit;
    args = [(UInt, "amount")];
    (*Return(If(Val(VBool(True)),StateAssign(This None, "blood", AritOp(Minus(StateRead(This None, "blood"),Var "amount"))),Val(VUnit))); *)
    body =  Return(Call(Cons("BloodBank", StateRead(This None, "bank")),"donate",Val(VUInt 0), [Var "amount"]))
  } in
  let getBank = {
    name = "getBank";
    rettype = C(1);
    args = [];
    body = Return(StateRead(This None, "bank"));
  } in
  let getBlood = {
    name = "getBlood";
    rettype = UInt;
    args = [];
    body = Return(StateRead(This None, "blood"));
  } in
  {
    name = "Donor";
    state = [(UInt, "blood"); (Address, "bank")];
    constructor = ([(UInt, "blood"); (Address,"bank")], (Seq(
        StateAssign(This None, "blood", Var("blood")),
        StateAssign(This None, "bank", Var("bank"))
      )));
    functions = [donate; getBank; getBlood];
  }

let eoa_contract () : contract_def =
  let fb = {
    name = "fb";
    rettype = Unit;
    args = [];
    body = Return(Val(VUnit));
  } in
  {
    name = "EOAContract";
    state = [];
    constructor = ([], Val(VUnit));
    functions = [fb];
  } *)

let eoa_contract () : contract_def =
  let fb = {
    name = "fb";
    rettype = Unit;
    annotation = None;
    args = [];
    body = (Val(VUnit));
  } in
  
  {
    name = "EOAContract";
    super_contracts = [];
    super_constructors_args = [];
    state = [];
    constructor = ([],Val VUnit);
    functions = [fb];
  }

let bank_contract () : contract_def =
  let deposit = {
    name = "deposit";
    annotation = None;
    rettype = Unit;
    args = [];
    body = 
        (StateAssign(
            This None,
            "balances",
            MapWrite(
              StateRead(This None,"balances"), MsgSender, AritOp((Plus(MapRead(StateRead(This None,"balances"),MsgSender), MsgValue))))))
  } in
  let getBalance = {
    name = "getBalance";
    rettype = UInt;
    annotation = None;
    args = [];
    body = Return(MapRead(StateRead(This None,"balances"),MsgSender))
  } in

  let getLiquidity = {
    name = "getLiquidity";
    rettype = UInt;
    annotation = None;
    args = [];
    body = Return(Balance(Address(This None)))
  }
  in
  let transfer = {
    name = "transfer";
    rettype = Unit;
    annotation = None;
    args = [(Address None, "to"); (UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
              Seq(StateAssign(This None, "balances", MapWrite(
                  StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
                  StateAssign(This None, "balances", MapWrite(
                      StateRead(This None,"balances"), Var("to"), AritOp(Plus(MapRead(StateRead(This None,"balances"),Var("to")), Var("amount")))))
                ),
              Val(VUnit))
  } in
  let withdraw = {
    name = "withdraw";
    rettype = Unit;
    annotation = None;
    args = [(UInt, "amount")];
    body = Return(If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
              Seq(
                StateAssign(This None, "balances", MapWrite(
                    StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
                Transfer(MsgSender, Var("amount"))
              ),
              Val(VUnit)
             ))
  } in
  {
    name = "Bank";
    super_contracts = [];
    super_constructors_args = [];
    state = [(Map(Address None, UInt),"balances")];
    constructor = ([], (Val VUnit));
    functions = [deposit; getBalance; transfer; withdraw; getLiquidity];
  }

let simple_bank_contract() = 
  let fb = {
      name = "fb";
      rettype = Unit;
      annotation = None;
      args = [];
      body = (Val(VUnit));
    } in
  {
    name = "SimpleBank";
    super_contracts = ["Bank"];
    super_constructors_args = [[]];
    state = []; (*(Map(Address None, UInt),"balances")*)
    constructor = ([], (Val VUnit));
    functions = [fb];
  }


  let bank_with_deposit_tracker_contract() = 
  let fb = {
      name = "fb";
      rettype = Unit;
      annotation = None;
      args = [];
      body =  ((StateAssign(
        This None,
        "tracker",AritOp(Plus(StateRead(This None, "tracker"), Val(VUInt 1))))));
    } in
    {
      name = "BankWithDepositTracker";
      super_contracts = ["Bank"];
      super_constructors_args = [[]];
      state = [(UInt, "tracker")]; (*(Map(Address None, UInt),"balances")*)
      constructor = ([], StateAssign(This None, "tracker",Val(VUInt 0)));
      functions = [fb];
    }


  let blood_bank_contract () : contract_def =
    let setHealth = {
      name = "setHealth";
      rettype = Unit;
      annotation = None;
      args = [(Address None, "donor"); (Bool, "isHealty")];
      body = Return (
          If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
             (StateAssign(
                 This None,
                 "healty",
                 MapWrite(
                   StateRead(This None,"healty"), Var("donor"), Var("isHealty")))),
             Revert
            )
        );
    } in
    let isHealty = {
      name = "isHealty";
      rettype = Bool;
      annotation = None;
      args = [(Address None, "donor")];
      body = Return(
          If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
             MapRead(StateRead(This None, "healty"), Var("donor")),
             Revert
            )
        );
    } in
    (* If(BoolOp(Conj(MapRead(StateRead(This None, "healty"), MsgSender), BoolOp(Conj(
              BoolOp(Greater(Var("donorBlood"),Val(VUInt(3000)))), BoolOp(Greater(
                  AritOp(Minus(Var("donorBlood"), Var("amount"))), Val(VUInt(0)))))))),
            Seq(StateAssign(This None, "blood", AritOp(Plus(StateRead(This None, "blood"), Var("amount")))),Val(VBool(True))),
            Val(VBool(False))) *)
    let donate = {
      (* |Call of expr * string * expr * expr list e.f.value(e)(le) *)
      name = "donate";
      rettype = Bool;
      annotation = None;
      args = [(UInt, "amount")];
      body = Return(
          Let(UInt, "donorBlood",Call(Cons("Donor", MsgSender),"getBlood",Val(VUInt(0)),[]),
              Seq(StateAssign(This None, "blood", AritOp(Plus(StateRead(This None, "blood"), Var("amount")))),Val(VBool(True)))))
      ;
    } in
    let getDoctor = {
      name = "getDoctor";
      rettype = Address None;
      annotation = None;
      args = [];
      body = Return(StateRead(This None, "doctor"));
    } in
    let getBlood = {
      name = "getBlood";
      rettype = UInt;
      annotation = None;
      args = [];
      body = Return(StateRead(This None, "blood"));
    } in
    {
      name = "BloodBank";
      super_contracts = [];
      super_constructors_args = [];
      state = [(Map(Address None, Bool), "healty"); (Address None, "doctor"); (UInt, "blood")];
      constructor = ([(Map(Address None, Bool), "healty"); (Address None, "doctor"); (UInt, "blood")],
                     (Seq((StateAssign(This None, "healty", Var("healty")),
                           Seq((StateAssign(This None, "doctor", Var("doctor"))),
                               StateAssign(This None, "blood", Var("blood")))))));
  
      (* constructor = ([], Val(VUnit));           *)
      functions = [setHealth; isHealty; donate; getDoctor; getBlood];
    }
  
  let donor_contract () : contract_def =
    let donate = {
      name = "donate";
      rettype = Unit;
      annotation = None;
      args = [(UInt, "amount")];
      (*Return(If(Val(VBool(True)),StateAssign(This None, "blood", AritOp(Minus(StateRead(This None, "blood"),Var "amount"))),Val(VUnit))); *)
      body =  Return(Call(Cons("BloodBank", StateRead(This None, "bank")),"donate",Val(VUInt 0), [Var "amount"]))
    } in
    let getBank = {
      name = "getBank";
      rettype = C(1);
      annotation = None;
      args = [];
      body = Return(StateRead(This None, "bank"));
    } in
    let getBlood = {
      name = "getBlood";
      rettype = UInt;
      annotation = None;
      args = [];
      body = Return(StateRead(This None, "blood"));
    } in
    {
      name = "Donor";
      (* is EOACONTRACT ?? *)
      super_contracts = [];
      super_constructors_args = [];
      state = [(UInt, "blood"); (Address None, "bank")];
      constructor = ([(UInt, "blood"); (Address None,"bank")], (Seq(
          StateAssign(This None, "blood", Var("blood")),
          StateAssign(This None, "bank", Var("bank"))
        )));
      functions = [donate; getBank; getBlood];
    }

