// ==UserScript==
// @name         MOHelper
// @namespace    http://tampermonkey.net/
// @version      0.2.1
// @description  Press Z for a brand new world!
// @author       Tony Xiang
// @license      AGPL-3.0
// @match        https://minesweeper.online/*
// @icon         data:image/gif;base64,R0lGODlhAQABAAAAACH5BAEKAAEALAAAAAABAAEAAAICTAEAOw==
// @require      https://hub.fastgit.xyz/T0nyX1ang/MOHelper/raw/master/solver.js
// @grant        none
// ==/UserScript==

function solveBoard() {
    // G68 in app.js contains sufficient information to solve the board
    if (G68.$ === 0) {
        alert(
            "Please select the correct page or wait until the page is fully loaded!"
        );
        return false;
    }
    let mines = G68.m1;
    let width = G68.s3;
    let height = G68.s4;
    let mineGrid = G68.c3.t;
    let mineCovered = G68.c3.o;
    let isNF = true;
    let board = new Board(1, width, height, mines, "", "safe");
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            const tile = board.getTileXY(x, y);
            const k = mineGrid[x * height + y];
            const c = mineCovered[x * height + y];
            if (k === 9) {
                // flag
                tile.toggleFlag();
                board.bombs_left--;
                isNF = false;
            } else if (k >= 0 && k <= 8 && c === 1) {
                // number
                tile.setValue(parseInt(k));
            } else if (k === 0 && c === 0) {
                // empty
                tile.setCovered(true);
            } else {
                // other situations
                alert("Failed to process, please check your board!");
                return false;
            }
        }
    }

    let result = solver(board, { verbose: false, playStyle: isNF ? 2 : 1 });
    result.then((value) => {
        let actions = value.actions;

        // next up, render tiles
        for (let i = 0; i < actions.length; i++) {
            let curAction = actions[i];
            let target_type = "";
            if (curAction.prob === 0 && curAction.action === ACTION_FLAG) {
                // bomb tiles
                target_type = "hint-flag";
            } else if (
                curAction.prob === 1 &&
                curAction.action === ACTION_CLEAR
            ) {
                target_type = "hint-to-open";
            } else if (curAction.action === ACTION_CLEAR) {
                target_type = "hint-extra";
            }
            let curX = curAction.x;
            let curY = curAction.y;
            let originalCell = document.getElementById(`cell_${curX}_${curY}`);
            originalCell.innerHTML = originalCell.outerHTML.replace(
                "_closed",
                "_closed " + target_type
            );
            if (target_type === "hint-extra") {
                originalCell.innerHTML = originalCell.innerHTML.replace(
                    "</div>",
                    parseInt(100 * (1 - curAction.prob)) + "</div>"
                ); // suboptimal solution
                if (i == 0) {
                    originalCell.innerHTML = originalCell.innerHTML.replace(
                        "_closed hint-extra",
                        "_closed hint-to-open"
                    ); // optimal solution
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
        return false;
    } catch (error) {
        alert(
            "Please select the correct page or wait until the page is fully loaded!"
        );
        return true;
    }
}

(function () {
    "use strict";
    let solver_status = false;
    document.addEventListener("keydown", function (e) {
        if (e.keyCode == 90 && !solver_status) {
            // Z Key
            solver_status = solveBoard();
        } else if ((e.keyCode == 88 || e.keyCode == 32) && solver_status) {
            // X Key
            solver_status = refreshBoard();
        }
    });

    document.addEventListener("mousedown", function (e) {
        if (solver_status) {
            solver_status = refreshBoard();
        }
    });

    const solve_btn = document.createElement("button");
    solve_btn.innerHTML = "Solve";
    solve_btn.onclick = function () {
      if (!solver_status) {
        solver_status = solveBoard();
      }
    };
    document.getElementById("seo").append(solve_btn);
})();
