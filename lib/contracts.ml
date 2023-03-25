open Types

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
    function_lookup_table = Hashtbl.create 64;
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
    args = [(Address CTop, "to"); (UInt, "amount")];
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
    state = [(Map(Address CTop, UInt),"balances")];
    constructor = ([], (Val VUnit));
    functions = [deposit; getBalance; transfer; withdraw; getLiquidity];
    function_lookup_table = Hashtbl.create 64;
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
    state = []; (*(Map(Address CTop, UInt),"balances")*)
    constructor = ([], (Val VUnit));
    functions = [fb];
    function_lookup_table = Hashtbl.create 64;
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
  
    let executeLiquidity = {
      name = "executeLiquidity";
      rettype = UInt;
      annotation = None;
      args = [];
      body = Return(This (Some("getLiquidity",[])))
    }
    in
    {
      name = "BankWithDepositTracker";
      super_contracts = ["Bank"];
      super_constructors_args = [[]];
      state = [(UInt, "tracker")]; (*(Map(Address CTop, UInt),"balances")*)
      constructor = ([], StateAssign(This None, "tracker",Val(VUInt 0)));
      functions = [fb; executeLiquidity];
      function_lookup_table = Hashtbl.create 64;
    }


  let blood_bank_contract () : contract_def =
    let setHealth = {
      name = "setHealth";
      rettype = Unit;
      annotation = None;
      args = [(Address CTop, "donor"); (Bool, "isHealty")];
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
      args = [(Address CTop, "donor")];
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
      rettype = Address CTop;
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
      state = [(Map(Address CTop, Bool), "healty"); (Address CTop, "doctor"); (UInt, "blood")];
      constructor = ([(Map(Address CTop, Bool), "healty"); (Address CTop, "doctor"); (UInt, "blood")],
                     (Seq((StateAssign(This None, "healty", Var("healty")),
                           Seq((StateAssign(This None, "doctor", Var("doctor"))),
                               StateAssign(This None, "blood", Var("blood")))))));
  
      (* constructor = ([], Val(VUnit));           *)
      functions = [setHealth; isHealty; donate; getDoctor; getBlood];
      function_lookup_table = Hashtbl.create 64;
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
      rettype = C("BloodBank");
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
      state = [(UInt, "blood"); (Address CTop, "bank")];
      constructor = ([(UInt, "blood"); (Address CTop,"bank")], (Seq(
          StateAssign(This None, "blood", Var("blood")),
          StateAssign(This None, "bank", Var("bank"))
        )));
      functions = [donate; getBank; getBlood];
      function_lookup_table = Hashtbl.create 64;
    }

