# systemverilog_snippets

## How to run 
```
echo "STARTING run.bash";
curl -o testbench.sv --no-sessionid -H "Cache-Control: no-cache" --tlsv1.2   <github URL to source file>;
cat testbench.sv;
vlib work && vlog '-timescale' '1ns/1ns' testbench.sv  && vsim -c -do "vsim +access+r; run -all; exit";
rm testbench.sv;
```
