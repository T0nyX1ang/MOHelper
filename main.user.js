// ==UserScript==
// @name         MOHelper
// @namespace    http://tampermonkey.net/
// @version      0.2.5
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
	let flagGrid = G68.c3.f;
	let isNF = true;
	let board = new Board(width, height, mines, "", "safe");
	for (let y = 0; y < height; y++) {
		for (let x = 0; x < width; x++) {
			const tile = board.getTileXY(x, y);
			const k = mineGrid[x * height + y];
			const c = mineCovered[x * height + y];
			const f = flagGrid[x * height + y];
			if (k === 9 || f === 1) {
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

	let result = solver(board, { verbose: false, playStyle: 2 });
	result.then((value) => {
		let actions = value.actions;

		// next up, render tiles
		for (let i = 0; i < actions.length; i++) {
			let curAction = actions[i];
			let target_type = "";
			if (curAction.prob === 0 && curAction.action === ACTION_FLAG) {
				// bomb tiles
				target_type = "hint-flag";
			} else if (curAction.prob === 1 && curAction.action === ACTION_CLEAR) {
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
	let lock = true;
	let timer = null;
	document.addEventListener("keydown", function (e) {
		if (e.code === "KeyZ" && !solver_status) {
			// Z key
			solver_status = solveBoard();
		} else if ((e.code === "KeyX" || e.code == "Space") && solver_status) {
			// X key
			solver_status = refreshBoard();
		}
	});

    document.addEventListener("mousedown", function (e) {
        if (solver_status) {
            solver_status = refreshBoard();
        }
    });

    if ("ontouchstart" in document.documentElement) {
        // special check for mobile devices
        document.addEventListener("touchstart", function (e) {
            if (timer !== null) {
                clearTimeout(timer);
            }
            timer = setTimeout(() => {
                lock = false;
                if (!solver_status) {
                    // left mouse key
                    solver_status = solveBoard();
                }
            }, 500);
        });

        document.addEventListener("touchend", function (e) {
            clearTimeout(timer);
            setTimeout(() => {
                lock = true;
                if (solver_status) {
                    solver_status = refreshBoard();
                }
            });
        });

        document.addEventListener("click", function (e) {
            if (lock && solver_status) {
                solver_status = refreshBoard();
            }
        });
    }
})();
