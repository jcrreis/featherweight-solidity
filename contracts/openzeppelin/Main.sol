import "./Game.sol";

contract Main {

    Game game;

    constructor() {
        this.game = new Game{value: 0}();
    }

    function fb() {

    }

    function run() {
       Game aux = this.game;

    }
}