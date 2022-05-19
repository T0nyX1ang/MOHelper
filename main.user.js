// ==UserScript==
// @name         MOHelper
// @namespace    http://tampermonkey.net/
// @version      0.1.9
// @description  Press Z for a brand new world!
// @author       Tony Xiang
// @license      AGPL-3.0
// @match        https://minesweeper.online/*
// @icon         data:image/gif;base64,R0lGODlhAQABAAAAACH5BAEKAAEALAAAAAABAAEAAAICTAEAOw==
// @require      https://github.com/T0nyX1ang/MOHelper/raw/main/solver.js
// @grant        none
// ==/UserScript==

async function mainSolver(data, mines) {
    const lines = data.split("\n");

    const width = lines[0].length;
    const height = lines.length;

    let board = new Board(1, width, height, mines, "", "safe");

    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            const char = lines[y].charAt(x);
            const tile = board.getTileXY(x, y);

            if (char == "F") {
                tile.toggleFlag();
                board.bombs_left--;
            } else if (char - "0" > -1 && char - "0" < 10) {
                tile.setValue(char - "0");
            } else {
                tile.setCovered(true);
            }
        }
    }

    let actions = await solver(board, {'verbose': false, 'playStyle': 2});
    return actions
}

function solveBoard() {
    let mineGrid = null;
    let isNF = true;
    let totalMines = 0;
    try {
        mineGrid = document.getElementById("A43").children;
        // if (document.querySelector(".replay-button-active") === null) {
        // alert("You can not solve a board when the game is not finished!")
        // return false;
        // }
        if (document.getElementById("top_area_mines_100").className.match("_top-area-num-") ||
            document.getElementById("top_area_mines_10").className.match("_top-area-num-")) {
            alert("Too much mines on board!");
            return false;
        }
        let mine_100 = document.getElementById("top_area_mines_100").className.match(/_top-area-num\d/)[0][13] - "0"; // digit 100
        let mine_10 = document.getElementById("top_area_mines_10").className.match(/_top-area-num\d/)[0][13] - "0"; // digit 10
        let mine_1 = document.getElementById("top_area_mines_1").className.match(/_top-area-num\d/)[0][13] - "0"; // digit 1
        totalMines = mine_100 * 100 + mine_10 * 10 + mine_1;
    } catch(error) {
        alert("Please select the correct page or wait until the page is fully loaded!")
        return false;
    }
    let board = new String();
    let len = mineGrid.length;
    for (let i = 0; i < len; i++) {
        let block = mineGrid[i].className;
        let process = true;
        if (block.match("clear")) {
            board += "\n";
        } else if (block.match("_flag")) {
            board += "F";
            isNF = false;
            totalMines++;
        } else if (block.match("_closed")) {
            board += "C";
        } else if (block.match(/_type1\d/)) {
            board += "?";
            process = false;
        } else {
            let found = block.match(/_type\d/)
            if (found) {
                board += found[0][5];
            } else {
                let found = block.match(/_rtype\d*/);
                if (found) {
                    let cvt_number = "";
                    for (let ci = 6; ci < found[0].length; ci++) {
                        cvt_number += found[0][ci];
                    }
                    let rev_table = {};
                    rev_table[0] = "0";
                    let fwd_table = R44.t29;
                    for (let v in fwd_table) {
                        rev_table[fwd_table[v]] = v;
                    }
                    board += rev_table[cvt_number];
                } else {
                    board += "?";
                    process = false;
                }
            }
        }
        if (process === false) {
            alert("Failed to process, please check your board!");
            return false;
        }
    }

    // console.log(totalMines);
    // console.log(board);
    let result = mainSolver(board.trim(), totalMines);
    result.then((value) => {
        let actions = value.actions;

        // next up, render tiles
        for (let i = 0; i < actions.length; i++) {
            let curAction = actions[i];
            let target_type = '';
            if (curAction.prob === 0 && curAction.action === ACTION_FLAG) {
                // bomb tiles
                target_type = 'hint-flag';
            } else if (curAction.prob === 1 && curAction.action === ACTION_CLEAR) {
                target_type = 'hint-to-open';
            } else if (curAction.action === ACTION_CLEAR) {
                target_type = 'hint-extra';
            }
            let curX = curAction.x;
            let curY = curAction.y;
            let originalCell = document.getElementById(`cell_${curX}_${curY}`);
            originalCell.innerHTML = originalCell.outerHTML.replace('_closed', '_closed ' + target_type);
            if (target_type === 'hint-extra') {
                originalCell.innerHTML = originalCell.innerHTML.replace('</div>', parseInt(100 * (1 - curAction.prob)) + '</div>'); // suboptimal
                if (i == 0) {
                    originalCell.innerHTML = originalCell.innerHTML.replace('_closed hint-extra', '_closed hint-to-open'); // optimal solution
                }
            }
        }
    });

    return true;
}

function refreshBoard() {
    try {
        let mineGrid = document.getElementById("A43").children;
        let len = mineGrid.length;
        for (let i = 0; i < len; i++) {
            mineGrid[i].innerHTML = "";
        }
        return false
    } catch(error) {
        alert("Please select the correct page or wait until the page is fully loaded!")
        return true;
    }
}

(function() {
    "use strict";
    let solver_status = false;
    document.addEventListener('keydown', function(e){
        if (e.keyCode == 90 && !solver_status) { // Z Key
            solver_status = solveBoard();
        } else if ((e.keyCode == 88 || e.keyCode == 32) && solver_status) { // X Key
            solver_status = refreshBoard();
        }
    })

    document.addEventListener('mousedown', function(e) {
        if (solver_status) {
            solver_status = refreshBoard();
        }
    })
})();
