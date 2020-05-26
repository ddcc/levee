This archive contains simple proof-of-concept prototype of SFI-based safe
region protection mechanism for CPI. The cpi-simple-sfi.patch file must be
applied on top of the levee early preview 0.2 release. In addition, the
kernel/loader must be modified to not allocate any objects (stack, mapped
libraries) in the upper half of the userspace. We will release the patch
that implements it for FreeBSD shortly.
