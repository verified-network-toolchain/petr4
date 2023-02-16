This folder contains the sources for generating the official Petr4 formalization document.

# Markup version

The markup version uses Madoko (https://www.madoko.net/) to produce
HTML and PDF versions of the documentation. Pre-built versions of the
documentation are available on the
[wiki](https://github.com/TODO/wiki).

Files:
- ```Petr4-spec.mdk``` is the main file. It is markup, with three custom
  environments: P4Example (code examples), P4Grammar (grammar
  fragments), and P4PseudoCode (P4 semantics described in pseudo-code).
- ```grammar.mdk``` is the whole grammar in a single file included at
  the end of the main file. TODO: 
- ```p4.json``` is providing custom syntax highlighting for P4. It is a rip
  off from the P4.json provided by P4 spec.
- ```Makefile``` builds documentation in the build subdirectory

## Building

Follow the instructions for various platforms below.

HINT: For *nix builds using make, you can use use `make html` for quicker turnarounds and `make` for the final htlp + PDF output.

### MacOS

We use the [local
installation](http://research.microsoft.com/en-us/um/people/daan/madoko/doc/reference.html#sec-installation-and-usage)
method. For Mac OS, I installed node.js using Homebrew and then Madoko
using npm:
```
brew install node.js
npm install madoko -g
```
Note that to build the PDF you need a functional TeX version installed.

Note if you have problems with linking node [this](https://stackoverflow.com/questions/31691626/cant-brew-install-node) is helpful.

If you check out the ```gh-pages``` branch of this repository, the
following two files can be found in the root directory.  You may
install them on a Mac using Font Book:

```
UtopiaStd-Regular.otf
luximr.ttf
```

### Linux

Follow the instruction below by hand, or for an Ubuntu 16.04 or 18.04
system, you may use the bash script
[`setup-for-ubuntu-linux.sh`](setup-for-ubuntu-linux.sh) to install
the necessary packages and fonts for you.

```
sudo apt-get install nodejs
sudo npm install madoko -g
make
```
In particular (on Ubuntu 16.04 at least), don't try `sudo apt-get install npm` because `npm` is already included and this will yield a bunch of confusing error messages from `apt-get`.

### Windows

You need to install miktex [http://miktex.org/], madoko
[https://www.madoko.net/] and node.js [https://nodejs.org/en/].  To
build you can invoke the make.bat script.

###
- https://fontsup.com/font/utopia-std-display.html
- https://www.fontsquirrel.com/fonts/luxi-mono
