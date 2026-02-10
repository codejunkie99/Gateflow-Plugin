## Design Patterns Reference

### Valid/Ready Handshake
```systemverilog
// Producer
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) valid <= 1'b0;
    else if (new_data) valid <= 1'b1;
    else if (ready) valid <= 1'b0;

// Consumer
assign ready = !full;
wire transfer = valid && ready;
```

### Skid Buffer
```systemverilog
// Allows ready to deassert without losing data
logic [WIDTH-1:0] skid_data;
logic skid_valid;

assign out_valid = in_valid || skid_valid;
assign out_data = skid_valid ? skid_data : in_data;
assign in_ready = !skid_valid;

always_ff @(posedge clk)
    if (in_valid && !out_ready && !skid_valid) begin
        skid_data <= in_data;
        skid_valid <= 1'b1;
    end else if (out_ready) begin
        skid_valid <= 1'b0;
    end
```

### 2FF Synchronizer
```systemverilog
logic [1:0] sync_ff;
always_ff @(posedge clk_dst or negedge rst_n)
    if (!rst_n) sync_ff <= '0;
    else sync_ff <= {sync_ff[0], async_in};
assign sync_out = sync_ff[1];
```

### Round-Robin Arbiter
```systemverilog
logic [$clog2(N)-1:0] last_grant;
logic [N-1:0] grant;

always_comb begin
    grant = '0;
    for (int i = 0; i < N; i++) begin
        int idx = (last_grant + 1 + i) % N;
        if (req[idx] && grant == '0) grant[idx] = 1'b1;
    end
end
```

### Async FIFO Pointers
```systemverilog
// Gray code conversion
function automatic [ADDR_W:0] bin2gray(input [ADDR_W:0] bin);
    return bin ^ (bin >> 1);
endfunction

// Pointer comparison (Gray domain)
assign full = (wr_gray[ADDR_W] != rd_gray_sync[ADDR_W]) &&
              (wr_gray[ADDR_W-1:0] == rd_gray_sync[ADDR_W-1:0]);
assign empty = (rd_gray == wr_gray_sync);
```

### Synchronous FIFO
```systemverilog
module sync_fifo #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             wr_en,
    input  logic [WIDTH-1:0] wr_data,
    input  logic             rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic             full,
    output logic             empty,
    output logic [$clog2(DEPTH):0] count
);
    localparam ADDR_W = $clog2(DEPTH);

    logic [WIDTH-1:0] mem [DEPTH];
    logic [ADDR_W:0] wr_ptr, rd_ptr;

    assign full  = (wr_ptr[ADDR_W] != rd_ptr[ADDR_W]) &&
                   (wr_ptr[ADDR_W-1:0] == rd_ptr[ADDR_W-1:0]);
    assign empty = (wr_ptr == rd_ptr);
    assign count = wr_ptr - rd_ptr;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
            rd_ptr <= '0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr[ADDR_W-1:0]] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
            if (rd_en && !empty) begin
                rd_ptr <= rd_ptr + 1;
            end
        end
    end

    assign rd_data = mem[rd_ptr[ADDR_W-1:0]];
endmodule
```

### Dual-Port RAM
```systemverilog
module dual_port_ram #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 1024
) (
    // Port A
    input  logic             clk_a,
    input  logic             en_a,
    input  logic             we_a,
    input  logic [$clog2(DEPTH)-1:0] addr_a,
    input  logic [WIDTH-1:0] din_a,
    output logic [WIDTH-1:0] dout_a,
    // Port B
    input  logic             clk_b,
    input  logic             en_b,
    input  logic             we_b,
    input  logic [$clog2(DEPTH)-1:0] addr_b,
    input  logic [WIDTH-1:0] din_b,
    output logic [WIDTH-1:0] dout_b
);
    (* ram_style = "block" *)
    logic [WIDTH-1:0] mem [DEPTH];

    // Port A
    always_ff @(posedge clk_a) begin
        if (en_a) begin
            if (we_a) mem[addr_a] <= din_a;
            dout_a <= mem[addr_a];
        end
    end

    // Port B
    always_ff @(posedge clk_b) begin
        if (en_b) begin
            if (we_b) mem[addr_b] <= din_b;
            dout_b <= mem[addr_b];
        end
    end
endmodule
```

### ROM with Initialization
```systemverilog
module rom #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 256,
    parameter string INIT_FILE = "rom_init.mem"
) (
    input  logic             clk,
    input  logic             en,
    input  logic [$clog2(DEPTH)-1:0] addr,
    output logic [WIDTH-1:0] data
);
    (* rom_style = "block" *)
    logic [WIDTH-1:0] mem [DEPTH];

    initial begin
        $readmemh(INIT_FILE, mem);
    end

    always_ff @(posedge clk) begin
        if (en) data <= mem[addr];
    end
endmodule
```

### Register File
```systemverilog
module reg_file #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 32,
    parameter int RD_PORTS = 2,
    parameter int WR_PORTS = 1
) (
    input  logic             clk,
    input  logic             rst_n,
    // Write ports
    input  logic [WR_PORTS-1:0]             wr_en,
    input  logic [WR_PORTS-1:0][$clog2(DEPTH)-1:0] wr_addr,
    input  logic [WR_PORTS-1:0][WIDTH-1:0]  wr_data,
    // Read ports
    input  logic [RD_PORTS-1:0][$clog2(DEPTH)-1:0] rd_addr,
    output logic [RD_PORTS-1:0][WIDTH-1:0]  rd_data
);
    logic [WIDTH-1:0] regs [DEPTH];

    // Writes
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++) regs[i] <= '0;
        end else begin
            for (int w = 0; w < WR_PORTS; w++) begin
                if (wr_en[w]) regs[wr_addr[w]] <= wr_data[w];
            end
        end
    end

    // Reads (combinational with bypass)
    always_comb begin
        for (int r = 0; r < RD_PORTS; r++) begin
            rd_data[r] = regs[rd_addr[r]];
            // Write-through bypass
            for (int w = 0; w < WR_PORTS; w++) begin
                if (wr_en[w] && (wr_addr[w] == rd_addr[r]))
                    rd_data[r] = wr_data[w];
            end
        end
    end
endmodule
```

---

## Error Handling & Fault Tolerance

### Planning Error Handling

```markdown
## Error Handling Plan

### Error Detection
| Mechanism | Use Case | Overhead |
|-----------|----------|----------|
| Parity | Single-bit errors | 1 bit per word |
| ECC (SECDED) | Memory protection | 7 bits per 64b |
| CRC | Packet integrity | 8-32 bits |
| Watchdog | System liveness | Timer logic |
| TMR | Critical paths | 3x area |

### Error Response
| Error Type | Detection | Response |
|------------|-----------|----------|
| Correctable | ECC/parity | Fix + log |
| Uncorrectable | ECC/CRC | Interrupt + flag |
| Timeout | Watchdog | Reset + recover |
| Protocol | Assertions | Error state |
```

### SECDED (Single Error Correct, Double Error Detect)
```systemverilog
module secded_encoder #(
    parameter int DATA_W = 64
) (
    input  logic [DATA_W-1:0] data_in,
    output logic [DATA_W+7:0] data_out  // 64 data + 8 check bits
);
    logic [7:0] check;

    // Hamming code calculation
    always_comb begin
        check[0] = ^(data_in & 64'h56AA_AD5B_56AA_AD5B);
        check[1] = ^(data_in & 64'h9B33_366C_D999_B366);
        check[2] = ^(data_in & 64'hE3C3_C78F_1E1E_3C78);
        check[3] = ^(data_in & 64'h03FC_07F0_0FE0_1FC0);
        check[4] = ^(data_in & 64'h03FF_F800_0FFF_E000);
        check[5] = ^(data_in & 64'hFC00_0000_FFFF_0000);
        check[6] = ^(data_in & 64'hFFFF_FFFF_0000_0000);
        check[7] = ^{data_in, check[6:0]};  // Overall parity
    end

    assign data_out = {check, data_in};
endmodule

module secded_decoder #(
    parameter int DATA_W = 64
) (
    input  logic [DATA_W+7:0] data_in,
    output logic [DATA_W-1:0] data_out,
    output logic              corrected,   // Single-bit error corrected
    output logic              error        // Double-bit error detected
);
    logic [7:0] syndrome;
    logic [DATA_W-1:0] data_corrected;
    logic parity_error;

    // Syndrome calculation (same as encoder)
    always_comb begin
        syndrome[0] = ^(data_in[DATA_W-1:0] & 64'h56AA_AD5B_56AA_AD5B) ^ data_in[DATA_W];
        syndrome[1] = ^(data_in[DATA_W-1:0] & 64'h9B33_366C_D999_B366) ^ data_in[DATA_W+1];
        syndrome[2] = ^(data_in[DATA_W-1:0] & 64'hE3C3_C78F_1E1E_3C78) ^ data_in[DATA_W+2];
        syndrome[3] = ^(data_in[DATA_W-1:0] & 64'h03FC_07F0_0FE0_1FC0) ^ data_in[DATA_W+3];
        syndrome[4] = ^(data_in[DATA_W-1:0] & 64'h03FF_F800_0FFF_E000) ^ data_in[DATA_W+4];
        syndrome[5] = ^(data_in[DATA_W-1:0] & 64'hFC00_0000_FFFF_0000) ^ data_in[DATA_W+5];
        syndrome[6] = ^(data_in[DATA_W-1:0] & 64'hFFFF_FFFF_0000_0000) ^ data_in[DATA_W+6];
        parity_error = ^data_in;
    end

    // Correct single-bit error
    always_comb begin
        data_corrected = data_in[DATA_W-1:0];
        if (syndrome != '0 && parity_error)
            data_corrected[syndrome[6:0]] = ~data_in[syndrome[6:0]];
    end

    assign data_out = data_corrected;
    assign corrected = (syndrome != '0) && parity_error;
    assign error = (syndrome != '0) && !parity_error;
endmodule
```

### Watchdog Timer
```systemverilog
module watchdog #(
    parameter int WIDTH = 24,
    parameter int WARN_THRESHOLD = 24'h800000,
    parameter int RESET_THRESHOLD = 24'hFFFFFF
) (
    input  logic clk,
    input  logic rst_n,
    input  logic kick,      // Reset counter
    input  logic enable,
    output logic warning,   // Counter near limit
    output logic timeout    // Counter expired
);
    logic [WIDTH-1:0] counter;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
        end else if (kick || !enable) begin
            counter <= '0;
        end else if (counter != RESET_THRESHOLD) begin
            counter <= counter + 1;
        end
    end

    assign warning = (counter >= WARN_THRESHOLD);
    assign timeout = (counter >= RESET_THRESHOLD);
endmodule
```

### Triple Modular Redundancy (TMR)
```systemverilog
module tmr_voter #(
    parameter int WIDTH = 32
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic [WIDTH-1:0] c,
    output logic [WIDTH-1:0] out,
    output logic             error  // Mismatch detected
);
    always_comb begin
        // Bitwise majority voting
        out = (a & b) | (b & c) | (a & c);
        error = (a != b) || (b != c) || (a != c);
    end
endmodule

module tmr_register #(
    parameter int WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q,
    output logic             error
);
    logic [WIDTH-1:0] q_a, q_b, q_c;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q_a <= '0;
            q_b <= '0;
            q_c <= '0;
        end else if (en) begin
            q_a <= d;
            q_b <= d;
            q_c <= d;
        end
    end

    tmr_voter #(.WIDTH(WIDTH)) u_voter (
        .a(q_a), .b(q_b), .c(q_c),
        .out(q), .error(error)
    );
endmodule
```

