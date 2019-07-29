# Curve13318 research

Implementation of Barreto's curve "Curve13318" for ARM Cortex M4. This code is
written for the STM32F407 device. The arithmetic used in this code is that of
<https://eprint.iacr.org/2018/286>.

## Reproducing benchmarks

```
# Install rust toolchain manager
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Set up rust
rustup toolchain install nightly-2019-07-01
rustup target add --toolchain nightly-2019-07-01 thumbv7em-none-eabi
rustup override set nightly-2019-07-01

# Build the project (takes a while)
cargo build --release

# Connect your ARM board now. Make sure you have user access; you can use the
# file listed below to achieve this.

# Launch openocd in a separate terminal
openocd --file openocd.cfg

# Run the project
cargo run --release

# GDB will automatically set a breakpoint on `Reset`, so we have to tell it
# to continue immediately.
>>> continue

# Now the benchmarking output should appear in the openocd console
```

If there is something that does not work, you may want to take a look at
`.cargo/config`. This file specifies how the code is being run. You can update
parameters here; for example the path to GDB.

## Udev access for users

Udev rules for allowing user access to st-link devices. Path: 
`/etc/udev/rules.d/70-st-link.rules`.

```
# STM32F3DISCOVERY rev A/B - ST-LINK/V2
ATTRS{idVendor}=="0483", ATTRS{idProduct}=="3748", TAG+="uaccess"

# STM32F3DISCOVERY rev C+ - ST-LINK/V2-1
ATTRS{idVendor}=="0483", ATTRS{idProduct}=="374b", TAG+="uaccess"
```

## Deployment on different devices

You can run this code on other `thumbv7em-none-eabi` devices! To achieve this, you will need to update the memory mapping to your own device in `memory.x`.
If you want to run the code on the `thumbv7em-none-eabihf` architecture, you
will need to update `.cargo/config`. We did not test this.

In any case, the setup is based on Jorge Aparicio's excellent guide on how to
set up Rust with ARM Cortex. You can find it at
<https://rust-embedded.github.io/cortex-m-quickstart/cortex_m_quickstart/>.