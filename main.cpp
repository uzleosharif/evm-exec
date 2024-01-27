// SPDX-License-Identifier: MIT

#include <fstream>
#include <print>
#include <ranges>
#include <stack>
#include <unordered_map>

#include <range/v3/all.hpp>
#include <magic_enum.hpp>
#include <intx/intx.hpp>

namespace {
constexpr std::size_t kHexBase{16};
constexpr std::size_t kWordSize{32};
constexpr std::size_t kByteSize{8};
constexpr std::size_t kMaxStackWordsSize{1024};
constexpr std::size_t kMaxStackSize{kMaxStackWordsSize * 8};
// TODO: 2^256
constexpr std::size_t kMemorySize{100'000};

using opcode_t = std::byte;
using word_t = intx::uint256;

constexpr opcode_t kShl{0x1b};
constexpr opcode_t kMLoad{0x51};
constexpr opcode_t kMStore{0x52};
constexpr opcode_t kJump{0x56};
constexpr opcode_t kJumpDest{0x5b};
constexpr opcode_t kPush0{0x5f};
constexpr opcode_t kPush1{0x60};
constexpr opcode_t kPush2{0x61};
constexpr opcode_t kPush12{0x6b};
constexpr opcode_t kDup2{0x81};
constexpr opcode_t kDup3{0x82};
constexpr opcode_t kSwap1{0x90};

enum class RevertError { kStackOverflow, kGasExceeded, kStackUnderflow, kMemoryUnalignedAccess, kInvalidJump };

struct OpcodeInfo {
  std::size_t advance_by{0};
  std::size_t gas_consumed{0};
};

std::unordered_map<opcode_t, OpcodeInfo> const kOpcodeInfo{
    {kMLoad, {}}, {kJump, {}}, {kDup3, {}}, {kPush2, {.advance_by = 2}}, {kPush0, {}}, {kPush12, {.advance_by = 12}}, {kPush1, {.advance_by = 1, .gas_consumed = 0}}, {kMStore, {}},
    {kSwap1, {}}, {kDup2, {}}, {kShl, {}}};

auto to_uint256(std::span<std::uint8_t const> byte_array) -> intx::uint256 {
  if (byte_array.size() > kWordSize) {
    throw std::invalid_argument{"Passed in byte array can not fit in uint256 object."};
  }

  intx::uint256 word{};
  for (auto const byte : byte_array) {
    word = (word << kByteSize) | byte;
  }
  return word;
}

// TODO: in following function templates, constrain template type via concept

// TODO: stack-contents array static??
template <std::size_t num_bytes>
auto PushToStack(auto&& execution_context) {
  // PUSHn <value>
  // Push n byte items (following opcode) on stack.

  intx::uint256 stack_item{0};

  if constexpr (num_bytes) {
    std::array<std::uint8_t, num_bytes> stack_item_bytes{};
    auto raw_data_span{std::span{std::next(std::begin(execution_context.bytecode), execution_context.program_counter + 1), num_bytes} |
                       std::views::transform([](auto byte) { return static_cast<std::uint8_t>(byte); })};
    std::ranges::copy(raw_data_span, std::begin(stack_item_bytes));
    stack_item = to_uint256(stack_item_bytes);
  }

  execution_context.stack.push(stack_item);

  if (execution_context.stack.size() > kMaxStackSize) {
    throw std::runtime_error{std::format("[PUSHn]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackOverflow))};
  }

  return execution_context;
}

auto Jump(auto&& execution_context) {
  // JUMP <counter>
  // Alter the program counter

  if (execution_context.stack.size() < 1) {
    throw std::runtime_error{std::format("[JUMP]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackUnderflow))};
  }

  auto const counter{execution_context.stack.top()};
  execution_context.stack.pop();

  execution_context.program_counter = static_cast<std::size_t>(counter);
  if (execution_context.bytecode.at(execution_context.program_counter) != kJumpDest) {
    throw std::runtime_error{std::format("[JUMP]: Revert due to {}.", magic_enum::enum_name(RevertError::kInvalidJump))};
  }

  return execution_context;
}

auto StoreToMemory(auto&& execution_context) {
  // MSTORE <offset> <value>
  // save word to memory

  if (execution_context.stack.size() < 2) {
    throw std::runtime_error{std::format("[MSTORE]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackUnderflow))};
  }

  auto const offset{execution_context.stack.top()};
  execution_context.stack.pop();

  auto const value{execution_context.stack.top()};
  execution_context.stack.pop();
  std::span<std::uint8_t const> value_bytes_span{intx::as_bytes(value), kWordSize};
  std::ranges::copy(value_bytes_span | std::views::reverse, std::next(std::begin(execution_context.memory), static_cast<std::size_t>(offset)));

  return execution_context;
}

auto LoadFromMemory(auto&& execution_context) {
  // MLOAD <offset>
  // Load word from memory

  if (execution_context.stack.size() < 1) {
    throw std::runtime_error{std::format("[MLOAD]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackUnderflow))};
  }

  auto const offset{execution_context.stack.top()};
  execution_context.stack.pop();
  auto value_span{std::span{std::next(std::begin(execution_context.memory), static_cast<std::size_t>(offset)), kWordSize}};
  execution_context.stack.push(to_uint256(value_span));

  return execution_context;
}

// TODO: SWAPn
auto SwapStackValues(auto&& execution_context) {
  // SWAP1 <a> <b>
  // Exchange 1st and 2nd stack items

  if (execution_context.stack.size() < 2) {
    throw std::runtime_error{std::format("[SWAPn]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackUnderflow))};
  }

  auto first{execution_context.stack.top()};
  execution_context.stack.pop();
  auto second{execution_context.stack.top()};
  execution_context.stack.pop();

  execution_context.stack.push(first);
  execution_context.stack.push(second);

  return execution_context;
}

// TODO: stack-contents array static??
template <std::size_t idx>
auto DuplicateStackValue(auto&& execution_context) {
  // DUPn <a> <b> ...
  // Duplicate [idx]th stack item

  // TODO: check stack should contain idx elements

  std::array<word_t, idx> stack_contents_window{};
  std::ranges::for_each(stack_contents_window, [&execution_context](auto& elem) {
    elem = execution_context.stack.top();
    execution_context.stack.pop();
  });

  std::ranges::for_each(stack_contents_window | std::views::reverse, [&execution_context](auto const& elem) { execution_context.stack.push(elem); });
  execution_context.stack.push(stack_contents_window.back());

  if (execution_context.stack.size() > kMaxStackSize) {
    throw std::runtime_error{std::format("[DUPn]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackOverflow))};
  }

  return execution_context;
}

auto ShiftLeft(auto&& execution_context) {
  // SHL <shift> <value>
  // Left shift operation

  if (execution_context.stack.size() < 2) {
    throw std::runtime_error{std::format("[SHL]: Revert due to {}.", magic_enum::enum_name(RevertError::kStackUnderflow))};
  }

  auto shift{execution_context.stack.top()};
  execution_context.stack.pop();
  auto value{execution_context.stack.top()};
  execution_context.stack.pop();

  execution_context.stack.push(value << shift);

  return execution_context;
}

}  // namespace

// TODO: Use a more performant data structure for stack_t (ideally we should be able to peek in the middle of stack randomly) that provides generic stack interface of push,pop,top,empty,size

class Interpreter final {
  using bytecode_t = std::vector<std::byte>;
  // NOTE: we prefer an arithmetic type for byte in defining memory structure
  using memory_t = std::array<std::uint8_t, kMemorySize>;
  using stack_t = std::stack<word_t>;

  struct ExecutionContext {
    std::size_t program_counter{0};
    bytecode_t bytecode{};
    stack_t stack{};
    memory_t memory{};
  };

 public:
  auto LoadBytecode(std::string_view bc_filepath) {
    m_execution_context.bytecode.clear();

    std::ifstream bc_ifs{bc_filepath};
    if (not bc_ifs.is_open()) {
      throw std::runtime_error(std::format("Could not find '{}' file.", bc_filepath).c_str());
    }

    auto bc_str{std::views::istream<char>(bc_ifs) | std::ranges::to<std::string>()};
    m_execution_context.bytecode.reserve(bc_str.size());
    m_execution_context.bytecode = bc_str | ranges::views::chunk(2) | ranges::views::transform([](auto const& chunk) {
                                     std::string byte_str{std::begin(chunk), std::end(chunk)};
                                     return static_cast<std::byte>(std::stoi(byte_str, nullptr, kHexBase));
                                   }) |
                                   ranges::to<std::vector>;
  }

  auto Interpret() {
    while (m_execution_context.program_counter < m_execution_context.bytecode.size()) {
      auto const& opcode{m_execution_context.bytecode.at(m_execution_context.program_counter)};

      try {
        m_execution_context = kOpcodeHandlers.at(opcode)(std::move(m_execution_context));

        m_execution_context.program_counter++;
        m_execution_context.program_counter += kOpcodeInfo.at(opcode).advance_by;
      } catch (std::out_of_range const& ex) {
        std::println("[ERROR] Unrecognized opcode: {:#x}", static_cast<std::uint8_t>(opcode));
        return;
      } catch (std::runtime_error const& ex) {
        std::println("[ERROR] {}", ex.what());
        return;
      }

      PrintStack();
      // PrintMemory();
    }

    // TODO: clear stack and initialize memory to 0 for next function call
  }

 private:
  ExecutionContext m_execution_context{};
  inline static std::unordered_map<opcode_t, ExecutionContext (*)(ExecutionContext&&)> const kOpcodeHandlers{{kJump, &Jump},
                                                                                                             {kDup3, &DuplicateStackValue<3>},
                                                                                                             {kPush2, &PushToStack<2>},
                                                                                                             {kPush0, &PushToStack<0>},
                                                                                                             {kMLoad, &LoadFromMemory},
                                                                                                             {kShl, &ShiftLeft},
                                                                                                             {kPush12, &PushToStack<12>},
                                                                                                             {kPush1, &PushToStack<1>},
                                                                                                             {kMStore, &StoreToMemory},
                                                                                                             {kSwap1, &SwapStackValues},
                                                                                                             {kDup2, &DuplicateStackValue<2>}};

  auto PrintStack() const -> void {
    std::println("printing stack contents ...");

    auto tmp_stack{m_execution_context.stack};
    while (not tmp_stack.empty()) {
      auto const top_word{tmp_stack.top()};
      auto const top_word_span{std::span{intx::as_bytes(top_word), kWordSize}};
      for (auto byte : top_word_span | std::views::reverse) {
        std::print("{:02x}, ", byte);
      }
      std::println("");

      tmp_stack.pop();
    }

    std::println("finished");
  }

  auto PrintMemory() -> void {
    constexpr static std::size_t kContentSize{300};

    std::println("printing (first {}) memory contents ...", kContentSize);
    std::ranges::for_each(std::views::iota(0) | std::views::take(kContentSize), [this](auto idx) { std::println("mem[{} = {:x}] = {:x}", idx, idx, m_execution_context.memory.at(idx)); });
    std::println("finished");
  }
};

auto main() -> int {
  Interpreter interpreter{};
  interpreter.LoadBytecode("/home/ush/evm_interpreter/data/smartcontracts/bin/HelloWorld.bin");
  interpreter.Interpret();
}
