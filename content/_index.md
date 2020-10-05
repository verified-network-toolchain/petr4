+++
title = "Composing Dataplane Programs with μP4"
description = "A compiler to build dataplane of network devices using portable, modular and composable programs."
+++

{{< lead >}}
Dataplane languages like P4 enable flexible and efficient packet-processing
using domain-specific primitives such as programmable parsers and match-action
tables. Unfortunately, P4 programs tend to be monolithic and tightly coupled to
the hardware architecture, which makes it hard to write programs in a portable
and modular way—e.g., by composing reusable libraries of standard protocols


To address this challenge, we present the design and implementation of a novel
framework (μP4) comprising a light-weight logical architecture that abstracts
away from the structure of the underlying hardware pipelines and naturally
supports powerful forms of program composition. Using examples, we show how μP4
enables modular programming. We present a prototype of the μP4 compiler that
generates code for multiple lower-level architectures, including Barefoot’s
Tofino Native Architecture.

{{< /lead >}}


## Goals
<div class="row py-3 mb-5">
	<div class="col-md-4">
		<div class="card flex-row border-0">
			<div class="mt-3">
				<span class="fas fa-project-diagram fa-2x text-primary"></span>
			</div>
			<div class="card-body pl-2">
				<h5 class="card-title">
					Portable
				</h5>
				<p class="card-text text-muted">
Programs written for one architecture, say PSA, should be easily reusable
across other architectures, say v1model, without having to modify the source
code. Following the “write-once, compile-anywhere” philosophy, programs should
be loosely coupled to architectures and use general constructs that a compiler
maps to architecture-specific constructs.
				</p>
			</div>
		</div>
	</div>
    <div class="col-md-4">
		<div class="card flex-row border-0">
			<div class="mt-3">
				<span class="fas fa fa-th fa-2x text-primary"></span>
			</div>
			<div class="card-body pl-2">
				<h5 class="card-title">
					Modular
				</h5>
				<p class="card-text text-muted">
It should be possible to develop individual packet-processing functions in an
independent manner agnostic of other dataplane functions. For example, one
should be able to define Ethernet and IPv4 packet-processing functionality as
separate module.
				</p>
			</div>
		</div>
	</div>
	<div class="col-md-4">
		<div class="card flex-row border-0">
			<div class="mt-3">
				<span class="fas fa fa-puzzle-piece fa-2x text-primary"></span>
			</div>
			<div class="card-body pl-2">
				<h5 class="card-title">
					Composable
				</h5>
				<p class="card-text text-muted">
It should be easy to flexibly compose individual functions to construct larger
dataplane programs. For example, imagine combining L2 Ethernet processing with
IPv4, or any other L3 routing scheme (e.g., IPv6, MPLS etc.) with compatible
interface and semantics, to obtain a modular router.
				</p>
			</div>
		</div>
	</div>
</div>

