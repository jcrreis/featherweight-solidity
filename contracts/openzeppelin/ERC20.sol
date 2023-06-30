import "./Context.sol";

contract ERC20 is Context {
    mapping(address => uint) balances;

    mapping(address => mapping(address => uint)) allowances;

    uint totalSupply;

    constructor() {}

    function fb() {}

    function decimals() returns (uint) {
        return 18;
    }

    function totalSupply() returns (uint) {
        return this.totalSupply;
    }

    function balanceOf(address account) returns (uint) {
        return this.balances[account];
    }

    function allowance(address owner, address spender) returns (uint) {
        return this.allowances[owner][spender];
    }

    function transferFrom(
        address from,
        address to,
        uint amount
    ) returns (bool) {
        address spender = this.msgSender();
        this.spendAllowance(from, spender, amount);
        this.transferTo(from, to, amount);
        return true;
    }

    function increaseAllowance(
        address spender,
        uint addedValue
    ) returns (bool) {
        address owner = this.msgSender();
        this.approve(
            owner,
            spender,
            this.allowance(owner, spender) + addedValue
        );
        return true;
    }

    function decreaseAllowance(
        address spender,
        uint requestedDecrease
    ) returns (bool) {
        address owner = this.msgSender();
        uint currentAllowance = this.allowance(owner, spender);
        if (currentAllowance < requestedDecrease) {
            revert;
        } else {
            this.approve(owner, spender, currentAllowance - requestedDecrease);
            return true;
        }
    }

    function transferTo(address from, address to, uint amount) {
        if ((from == address(0)) || (to == address(0))) {
            revert;
        } else {
            this.update(from, to, amount);
        }
    }

    function update(address from, address to, uint amount) {
        if (from == address(0)) {
            this.totalSupply = this.totalSupply + amount;
            if (to == address(0)) {
                this.totalSupply = this.totalSupply - amount;
            } else {
                this.balances = (this.balances[to] =
                    this.balances[to] +
                    amount);
            }
        } else {
            uint fromBalance = this.balances[from];
            if (fromBalance < amount) {
                revert;
            } else {
                this.balances = (this.balances[from] = fromBalance - amount);
                if (to == address(0)) {
                    this.totalSupply = this.totalSupply - amount;
                } else {
                    this.balances = (this.balances[to] =
                        this.balances[to] +
                        amount);
                }
            }
        }
    }

    function mint(address account, uint amount) {
        if (account == address(0)) {
            revert;
        } else {
            this.update(address(0), account, amount);
        }
    }

    function burn(address account, uint amount) {
        if (account == address(0)) {
            revert;
        } else {
            this.update(account, address(0), amount);
        }
    }

    function approve(address owner, address spender, uint amount) {
        if ((owner == address(0)) || (spender == address(0))) {
            revert;
        } else {
            mapping(address => uint) aux = this.allowances[owner];
            this.allowances = (this.allowances[owner] = (aux[
                spender
            ] = amount));
        }
    }

    function spendAllowance(address owner, address spender, uint amount) {
        uint currentAllowance = this.allowance(owner, spender);
        if (currentAllowance < amount) {
            revert;
        } else {
            this.approve(owner, spender, currentAllowance - amount);
        }
    }
}
