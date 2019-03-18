# Types and Programming Languages -- Exercises

Solutions to the exercises in and miscellaneous material for the book "Types
and Programming Languages" by Benjamin C. Pierce.

## Requirements

* `latex` distribution (e.g. [TeX Live](https://tug.org/texlive/))
* [`pandoc`](http://pandoc.org/)
* [`GNU Make`](https://www.gnu.org/software/make/)
* [`idris`](https://www.idris-lang.org/) (if you want to run the miscellaneous
  programs)

## Installation

    git clone https://github.com/mr-infty/tapl.git
    cd tapl

## Usage

Run

    make

to typeset the exercise solutions. These are organized into subdirectories
`ch-03`, `ch-04`, ... corresponding to chapters.

Some chapters are also accompanied by Idris programs (`*.idr`) that I wrote to
test my understanding. These probably aren't too well documented. Read at your
own risk.
