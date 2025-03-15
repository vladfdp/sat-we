# SAT-WE: SAT-based Witness-Like Encryption

A proof of concept for an almost witness encryption scheme

## Overview

This library implements a protocol that allows encrypting messages that can only be decrypted by someone who has commited to a witness satisfying a CNF-SAT formula. Unlike true witness encryption, this implementation works only for pre-committed data (the receiver must commit to their data first)

## Basic Usage Example

The `basic_usage.rs` example demonstrates:
1. Creating a polynomial commitment to a number (41) encoded as bits
2. Creating a condition (number < 50) as a CNF formula
3. Encrypting a message using this condition
4. Decrypting with the original polynomial

## Original Motivation

For more details, check out the blog post:
[SAT-based Witness Encryption](https://hackmd.io/@vladfdp/BJcQDpbrJl)