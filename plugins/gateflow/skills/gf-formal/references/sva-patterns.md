# SVA Property Patterns

## No Overflow (FIFO/Counter)
```systemverilog
a_no_overflow: assert property (
    @(posedge clk) disable iff (rst)
    full |-> !wr_en
);
```

## No Underflow
```systemverilog
a_no_underflow: assert property (
    @(posedge clk) disable iff (rst)
    empty |-> !rd_en
);
```

## Valid/Ready Handshake
```systemverilog
a_valid_stable: assert property (
    @(posedge clk) disable iff (rst)
    (valid && !ready) |=> valid
);

a_data_stable: assert property (
    @(posedge clk) disable iff (rst)
    (valid && !ready) |=> $stable(data)
);
```

## One-Hot (Mutual Exclusion)
```systemverilog
a_state_onehot: assert property (
    @(posedge clk) disable iff (rst)
    $onehot(state)
);
```

## Liveness (Request Granted)
```systemverilog
a_req_granted: assert property (
    @(posedge clk) disable iff (rst)
    req |-> ##[1:MAX_LATENCY] grant
);
```

## Reset Behavior
```systemverilog
a_reset_outputs: assert property (
    @(posedge clk)
    rst |-> (data_out == '0) && (count == '0)
);
```

## FIFO Count Tracking
```systemverilog
a_fifo_count_inc: assert property (
    @(posedge clk) disable iff (rst)
    (wr_en && !rd_en && !full) |=> (count == $past(count) + 1)
);
```
