# Tool for I/O Specification Generation

The `src` directory contains the source code of our tool to generate I/O specifications from a Tamarin theory file. Note that it is a fork of Tamarin itself to reuse the parsing of input files.
The `example-config-files` directory contains examples of configuration files to customize the operations of our tool.

To build & execute our tool, [Haskell Stack](https://docs.haskellstack.org/en/stable/README) must be installed.

## Generating I/O Specification
Our tool must first be built using
```
stack build
```

Before using a Tamarin theory file as input to our tool, it should be verified in Tamarin first.
Running the following command in the `src` folder will create I/O specifications for the Gobra verifier (`stack build` must have been executed):
```
stack exec -- tamarin-prover --tamigloo-compiler ../example-config-files/dh_gobra_config.txt
```
Note that the input Tamarin theory file is specified as `input_file` in the configuration file.
Furthermore, `base_dir` specifies the output directory for the files containing the generated IO specification.

The following command will instead generate I/O specifications for the VeriFast verifier (`stack build` must have been executed):
```
stack exec -- tamarin-prover --tamigloo-compiler ../example-config-files/dh_verifast_config.txt
```
