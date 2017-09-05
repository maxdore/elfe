# Interactive Theorem Proving for Students

This tool is meant for students to practice writing mathematical proofs. Several background libraries for sets, relations and functions have been implemented such that you can directly start writing a proof.

To get started, you best take a look at the [tutorial](https://elfe-prover.org/downloads/tutorial.pdf)  in the directory web/downloads and the examples directory.

## How does it work?

Internally, the mathematical text is transformed into a sequence of first-order formulas. This representation implies certain proof obligations which are checked by Automated Theorem Provers.
 
The technique is described [here](https://elfe-prover.org/downloads/thesis.pdf).

## Installation

You can try Elfe online [here](https://elfe-prover.org).

In order to install Elfe locally, you first need to copy `Settings-example.hs` to `Settings.hs` and adjust it to your needs (the automated theorem provers need to be installed separately. You may want to use [online-atps](https://github.com/jonaprieto/online-atps) for a quick start).

Then run `cabal install` to install all dependencies. The command line interface of Elfe is then located in `dist/build/elfe/elfe`, the executable `dist/build/elfe-server/elfe-server` starts a server to the web interface.

For development, you may want to run the programs interactively. You can do this easily by executing `./elfe.sh` respectively `./elfe-server.sh` 

## Usage

The command line interface expects a file to check, i.e. you can call

`elfe theorem.elfe`

to check the file `theorem.elfe`. In order to use the web interface, simply call `elfe-server`. The program will tell on which port its running, probably 8000. You can then call it in your web browser with

`localhost:8000`


## Get involved

You want to improve Elfe or implement new background libraries? Just create a pull request. If you want to do a larger project with Elfe, e.g., work on it with your thesis, you best get in touch with us at dev@elfe-prover.org.
