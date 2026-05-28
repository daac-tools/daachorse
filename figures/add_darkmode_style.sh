#!/bin/bash
# This program modifies the speed comparison figure to render in white in dark mode.
FIGURE_PATH="$(dirname "$0")/comparison.svg"
cat <(head -n 2 "${FIGURE_PATH}") <(echo "<style>
.fill { fill: rgb(0%, 0%, 0%); }
.stroke { stroke: rgb(0%, 0%, 0%); }
@media (prefers-color-scheme: dark) {
.fill { fill: rgb(100%, 100%, 100%); }
.stroke { stroke: rgb(100%, 100%, 100%); }
}
</style>") <(tail -n +3 "${FIGURE_PATH}" | sed "s/ fill=\"rgb(0%, 0%, 0%)\"/ class=\"fill\"/g" | sed "s/ stroke=\"rgb(0%, 0%, 0%)\"/ class=\"stroke\"/g") > "${FIGURE_PATH}.tmp"
mv "${FIGURE_PATH}.tmp" "${FIGURE_PATH}"
