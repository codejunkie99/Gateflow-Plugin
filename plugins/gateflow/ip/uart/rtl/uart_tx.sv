module uart_tx #(
    parameter int CLK_FREQ  = 100_000_000,
    parameter int BAUD_RATE = 115200
) (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] tx_data,
    input  logic       tx_valid,
    output logic       tx_ready,
    output logic       tx_out
);
    localparam int CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;
    localparam int CNT_W = $clog2(CLKS_PER_BIT);

    typedef enum logic [1:0] {IDLE, START, DATA, STOP} state_t;
    state_t state;
    logic [CNT_W-1:0] clk_cnt;
    logic [2:0] bit_idx;
    logic [7:0] tx_shift;

    assign tx_ready = (state == IDLE);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state    <= IDLE;
            tx_out   <= 1'b1;
            clk_cnt  <= '0;
            bit_idx  <= '0;
            tx_shift <= '0;
        end else begin
            unique case (state)
                IDLE: begin
                    tx_out <= 1'b1;
                    if (tx_valid) begin
                        tx_shift <= tx_data;
                        state    <= START;
                        clk_cnt  <= '0;
                    end
                end
                START: begin
                    tx_out <= 1'b0;
                    if (clk_cnt == CLKS_PER_BIT[CNT_W-1:0] - 1) begin
                        clk_cnt <= '0;
                        bit_idx <= '0;
                        state   <= DATA;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
                DATA: begin
                    tx_out <= tx_shift[bit_idx];
                    if (clk_cnt == CLKS_PER_BIT[CNT_W-1:0] - 1) begin
                        clk_cnt <= '0;
                        if (bit_idx == 3'd7) state <= STOP;
                        else bit_idx <= bit_idx + 1'b1;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
                STOP: begin
                    tx_out <= 1'b1;
                    if (clk_cnt == CLKS_PER_BIT[CNT_W-1:0] - 1) begin
                        clk_cnt <= '0;
                        state   <= IDLE;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
            endcase
        end
    end
endmodule
