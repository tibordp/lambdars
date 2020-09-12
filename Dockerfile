FROM rustlang/rust:nightly as build
RUN rustup target add x86_64-unknown-linux-musl

RUN USER=root cargo new --bin lambdars --vcs none

WORKDIR /lambdars
COPY ./Cargo.* ./
RUN cargo build --release --target=x86_64-unknown-linux-musl
RUN rm src/*.rs

COPY ./src ./src
RUN rm ./target/x86_64-unknown-linux-musl/release/deps/lambdars*
RUN cargo build --release --target=x86_64-unknown-linux-musl

# our final base
FROM scratch
COPY --from=build /lambdars/target/x86_64-unknown-linux-musl/release/lambdars /lambdars
ENTRYPOINT ["/lambdars"]