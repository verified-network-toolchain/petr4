+++
title = "Installing μP4"
description = ""
weight = 1
+++

{{< lead >}}
This webpage provides instructions to build and install μP4, and reproduce the results from the paper "Composing Dataplane Programs with μP4".

1. [As a pre-built VM](#pre-built-vm).
2. [Building and installing μP4 from source](#from-source).

**Note**: μP4 supports both v1model and Barefoot's TNA architectures. For
compiling programs for v1model, all the dependencies are publicly available.
However, if you would like to compile programs for TNA, you would need access
to Barefoot's proprietary SDE (version 9.0.0). Accordingly, the pre-built VM
has tools to support only the v1model. You would need to install Barefoot's SDE
yourself to support TNA.

## Pre-built VM

We provide a VM with μP4, along with all the dependencies, pre-installed here: [μP4 VM (2.8 GB)](https://drive.google.com/file/d/1-z0oF_SZHLxzGr4Cn6Bb1bUTEZJwFs93/view?usp=sharing) (md5sum: `95dd2959f71970d648f32be3a6144cf9`).
1. Install and start [Virtualbox](https://www.virtualbox.org/wiki/Downloads) on your machine.
2. Download μP4 VM image, and import it to Virtualbox by selecting  "File" -> "Import Appliance" in Virtualbox. If prompted, it's safe to ignore warnings related to Virtualbox Guest Additions.
3. Allocate the VM as much RAM as possible (at least 2GB) and two processors. Building `p4c` and `BMv2` software switch from source can be resource intensive. The VM comes with these pre-built and installed. In case you want to rebuild them within the VM, allocate more resources.
4. You may need to turn on virtualization extensions in your BIOS to enable 64-bit virtualization.
5. When the VM starts up, the `microp4` user should be automatically logged in. (username: `microp4`, password: `microp4`).
6. (Optional) Get the latest version of μP4: `cd microp4 && git pull --recurse-submodules`. Then, to build it, do `cd build && make -j2`. (The complete build instructions are here https://github.com/cornell-netlab/MicroP4#22-build-and-install-%CE%BCp4c in case you would like to build it from scratch. p4c and BMv2 software switch are already installed on the VM, and you would not need to re-build them normally.)
7. Next step: you can directly jump to building and testing composed programs by following the instructions here: https://github.com/cornell-netlab/MicroP4/tree/master/extensions/csa/msa-examples.

**Video**: We have also shared a video illustrating the steps and what to expect here:
{{< youtube ZtmLH0UFeqw >}}


**Note**: The VM does not include Barefoot's SDE. You will need to install it yourself on your local machine and compile the generated P4 programs following the instructions provided with the SDE. We have tested the Tofino backend with a native OS installation only, and not with the VM.

## From Source
We have released the source code for μP4 at https://github.com/cornell-netlab/MicroP4/ under an open-source license.

To build and install μP4, follow the instructions at:
https://github.com/cornell-netlab/MicroP4/tree/master#getting-started.

**Video**: We have also shared a video illustrating the steps and what to expect. We used these steps to build the VM mentioned above.
{{< youtube HI8LAPIx15Y >}}

{{< /lead >}}


